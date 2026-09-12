#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Run under palomar-no-unix to exercise the actual inherited syscall filter."""
import ctypes
import errno
import platform
import socket

with socket.socket(socket.AF_INET, socket.SOCK_STREAM):
    pass
for call in [lambda: socket.socket(socket.AF_UNIX), lambda: socket.socketpair(socket.AF_UNIX)]:
    try:
        call()
    except OSError as error:
        assert error.errno == errno.EPERM, error
    else:
        raise SystemExit('AF_UNIX unexpectedly permitted')
# Upper bits must not bypass the kernel's int-valued domain check.
sys_socket = {'x86_64': 41, 'aarch64': 198}[platform.machine()]
libc = ctypes.CDLL(None, use_errno=True)
result = libc.syscall(ctypes.c_long(sys_socket), ctypes.c_uint64((1 << 32) | socket.AF_UNIX),
                      ctypes.c_int(socket.SOCK_STREAM), ctypes.c_int(0))
assert result == -1 and ctypes.get_errno() == errno.EPERM
print('Socket filter passed: AF_INET allowed; AF_UNIX socket/socketpair and upper-bit bypass rejected.')
