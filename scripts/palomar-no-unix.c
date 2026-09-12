/* SPDX-License-Identifier: Apache-2.0
 * Developed with AI assistance; see ACKNOWLEDGEMENTS.md.
 * Apply Comparator's documented AF_UNIX restriction without requiring systemd.
 * Landrun still supplies filesystem isolation. libseccomp handles syscall ABI
 * translation; the mask follows the kernel's 32-bit socket-domain argument.
 * API references: https://github.com/seccomp/libseccomp/tree/main/doc/man/man3
 */
#include <errno.h>
#include <seccomp.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: palomar-no-unix COMMAND [ARGUMENTS...]\n");
        return 126;
    }
    scmp_filter_ctx ctx = seccomp_init(SCMP_ACT_ALLOW);
    if (ctx == NULL) {
        fprintf(stderr, "could not initialize the socket filter\n");
        return 126;
    }
    int rc = seccomp_rule_add(ctx, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(socket), 1,
                             SCMP_A0(SCMP_CMP_MASKED_EQ, UINT32_MAX, AF_UNIX));
    if (rc == 0)
        rc = seccomp_rule_add(ctx, SCMP_ACT_ERRNO(EPERM), SCMP_SYS(socketpair), 1,
                             SCMP_A0(SCMP_CMP_MASKED_EQ, UINT32_MAX, AF_UNIX));
    if (rc == 0)
        rc = seccomp_load(ctx);
    seccomp_release(ctx);
    if (rc < 0) {
        fprintf(stderr, "could not load the socket filter: %s\n", strerror(-rc));
        return 126;
    }
    execvp(argv[1], argv + 1);
    perror("could not execute the filtered command");
    return 127;
}
