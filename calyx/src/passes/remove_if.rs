use crate::errors;
use crate::lang::{
    ast, ast::Control, ast::Port, component::Component, context::Context,
};
use crate::passes::visitor::{Action, Named, VisResult, Visitor};

/// Pass that removes if statments where both branches are enables:
/// ```lisp
///    (if (@ cond port) (comps ...)
///        (enable A B ...)
///        (enable C B ...))
/// ```
/// It does this by connecting the condition port to all
/// the `valid` ports of the registers in the true branch
/// and connecting the inverse of the condition port to
/// the `valid` ports of the registers in the false branch
///
/// This pass currently does not support memories or other side
/// effecting components.
#[derive(Default)]
pub struct RemoveIf {}

impl Named for RemoveIf {
    fn name() -> &'static str {
        "remove-if"
    }

    fn description() -> &'static str {
        "remove simple if statements"
    }
}

impl Visitor for RemoveIf {
    fn finish_if(
        &mut self,
        con: &ast::If,
        this_comp: &mut Component,
        ctx: &Context,
    ) -> VisResult {
        match (&*con.tbranch, &*con.fbranch) {
            (
                Control::Enable { data: tbranch },
                Control::Enable { data: fbranch },
            ) => {
                if tbranch.comps.len() > 1 || fbranch.comps.len() > 1 {
                    return Ok(Action::Continue);
                }

                // get node and port for the comparison component
                let (cmp_name, cmp_idx, cmp_port) = match &con.port {
                    Port::Comp { component, port } => (
                        component.to_string(),
                        this_comp.structure.get_inst_index(&component)?,
                        port,
                    ),
                    Port::This { port } => (
                        "this".into(),
                        this_comp.structure.get_io_index(&port)?,
                        port,
                    ),
                };

                let (creg_name, creg_idx, creg_port) = {
                    let name =
                        format!("{}_{}_reg", cmp_name, cmp_port.to_string());
                    let reg_comp = ctx.instantiate_primitive(
                        &name,
                        &"std_reg".into(),
                        &[1, 1],
                    )?;
                    let reg_idx = this_comp.structure.add_primitive(
                        &name.clone().into(),
                        "std_reg",
                        &reg_comp,
                        &[1, 1],
                    );

                    this_comp
                        .structure
                        .insert_edge(cmp_idx, &cmp_port, reg_idx, "in")?;

                    let reg_first_port =
                        &this_comp.structure.graph[reg_idx].out_ports().next();
                    let reg_port = match reg_first_port {
                        Some(p) => p.clone(),
                        None => {
                            return Err(errors::Error::NotFoundPort(
                                "out".to_string(),
                                ast::Id::from(name),
                            ))
                        }
                    };

                    (name, reg_idx, reg_port)
                };

                let (cneg_name, cneg_idx, cneg_port) = {
                    let name = format!("{}_not", creg_name);
                    let neg_comp = ctx.instantiate_primitive(
                        &name,
                        &"std_not".into(),
                        &[1],
                    )?;
                    let neg_idx = this_comp.structure.add_primitive(
                        &name.clone().into(),
                        "std_not",
                        &neg_comp,
                        &[1],
                    );

                    this_comp
                        .structure
                        .insert_edge(creg_idx, &creg_port, neg_idx, "in")?;

                    let neg_first_port =
                        &this_comp.structure.graph[neg_idx].out_ports().next();
                    let neg_port = match neg_first_port {
                        Some(p) => p.clone(),
                        None => {
                            return Err(errors::Error::NotFoundPort(
                                "out".to_string(),
                                ast::Id::from(name),
                            ))
                        }
                    };

                    (name, neg_idx, neg_port)
                };

                let cor_idx = {
                    let name = format!("{}_or", creg_name);
                    let or_comp = ctx.instantiate_primitive(
                        &name,
                        &"std_or".into(),
                        &[1],
                    )?;
                    this_comp.structure.add_primitive(
                        &name.into(),
                        "std_or",
                        &or_comp,
                        &[1],
                    )
                };

                let add_structure_tbranch =
                    |this_comp: &mut Component, en_comp: &ast::Id| {
                        this_comp.structure.insert_edge(
                            creg_idx,
                            &creg_port,
                            this_comp.structure.get_inst_index(en_comp)?,
                            "valid",
                        )?;
                        this_comp.structure.insert_edge(
                            this_comp.structure.get_inst_index(en_comp)?,
                            "ready",
                            cor_idx,
                            "left",
                        )
                    };

                let add_structure_fbranch =
                    |this_comp: &mut Component, en_comp: &ast::Id| {
                        this_comp.structure.insert_edge(
                            cneg_idx,
                            &cneg_port,
                            this_comp.structure.get_inst_index(en_comp)?,
                            "valid",
                        )?;
                        this_comp.structure.insert_edge(
                            this_comp.structure.get_inst_index(en_comp)?,
                            "ready",
                            cor_idx,
                            "right",
                        )
                    };

                // tbranch.comp either has one component or empty
                let mut branch_control: Vec<ast::Id> = vec![];
                let mut branchs = vec![tbranch.clone(), fbranch.clone()];
                for (i, branch) in branchs.iter_mut().enumerate() {
                    if branch.comps.is_empty() {
                        let cconst_name = format!("{}_const", creg_name);
                        let cconst_comp = ctx.instantiate_primitive(
                            &cconst_name.clone(),
                            &"std_const".into(),
                            &[1, 1],
                        )?;
                        this_comp.structure.add_primitive(
                            &cconst_name.clone().into(),
                            "std_const",
                            &cconst_comp,
                            &[1, 1],
                        );
                        branch.comps.push(ast::Id::from(cconst_name));
                    }
                    let en_comp = &branch.comps[0];
                    if i == 0 {
                        add_structure_tbranch(this_comp, en_comp)?;
                    } else {
                        add_structure_fbranch(this_comp, en_comp)?;
                    }
                    branch_control.push(en_comp.clone())
                }

                branch_control.push(ast::Id::from(cneg_name));
                branch_control.push(ast::Id::from(creg_name.clone()));

                let mut cond_control = con.cond.clone();
                cond_control.push(ast::Id::from(creg_name));
                let comps_seq = vec![
                    Control::enable(cond_control),
                    Control::enable(branch_control),
                ];

                Ok(Action::Change(Control::seq(comps_seq)))
            }
            _ => Ok(Action::Continue),
        }
    }
}

/*fn resolve_signature<'a>(
    this_comp: &'a mut Component,
    en_comp: &ast::Id,
) -> Result<&'a ast::Signature, errors::Error> {
    let sig = this_comp.resolved_sigs.get(en_comp);
    match sig {
        Some(sig) => Ok(sig),
        None => Err(errors::Error::UndefinedComponent(en_comp.clone())),
    }
}*/
