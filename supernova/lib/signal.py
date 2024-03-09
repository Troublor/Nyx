import signal
import sys

_interrupted: bool = False


def interrupt():
    sys.stderr.write("Interrupted\n")
    global _interrupted
    _interrupted = True


def interrupted() -> bool:
    global _interrupted
    return _interrupted


def register_interrupt_handler():
    signal.signal(signal.SIGINT, lambda sig, frame: interrupt())
    signal.signal(signal.SIGTERM, lambda sig, frame: interrupt())
