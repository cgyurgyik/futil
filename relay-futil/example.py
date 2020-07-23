from tvm import relay
import relay2futil
import sys


def identity():
    """The float32 identity function in Relay.
    """
    x = relay.var('x', shape=())
    f = relay.Function([x], x)
    return f


def const():
    """A simple constant function in Relay.
    """
    return relay.Function([], relay.const(42))


def add():
    """Add together two constants in Relay.
    """
    return relay.Function([], relay.add(relay.const(37), relay.const(5)))

def add_var():
    """Add together two variables
    """
    x = relay.var('x', shape=())
    y = relay.var('y', shape=())
    return relay.Function([x, y], relay.add(x, y))

def assign():
    """Assign a const to a varible
    """
    x = relay.var('x', shape=())
    v1 = relay.log(x)
    v2 = relay.add (v1,x)
    return relay.Function([x], v2)
ALL_FUNCS = [identity, const, add, add_var, assign]


def simple_example():
    # See if the command line contains a function name.
    for option in ALL_FUNCS:
        if option.__name__ in sys.argv[1:]:
            func = option()
            break
    else:
        func = add()  # The default for no argument.

    if '-r' in sys.argv[1:]:
        # Dump the Relay representation (for educational purposes).
        print(func)
    else:
        # Compile the function and print the FuTIL.
        print(relay2futil.compile(func))


if __name__ == '__main__':
    simple_example()