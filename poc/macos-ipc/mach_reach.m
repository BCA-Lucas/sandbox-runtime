// Minimal mach-service reachability check (authorized bug-bounty PoC).
// For each service name on argv, call bootstrap_look_up and report only whether
// a send right was returned (REACHABLE) or the lookup was refused. No message is
// sent and no data is read; this establishes which service NAMES the Seatbelt
// profile's mach-lookup allowlist actually admits.
#include <mach/mach.h>
#include <servers/bootstrap.h>
#include <stdio.h>

int main(int argc, const char **argv) {
  for (int i = 1; i < argc; i++) {
    mach_port_t p = MACH_PORT_NULL;
    kern_return_t kr = bootstrap_look_up(bootstrap_port, argv[i], &p);
    printf("%-40s %s (kr=%d)\n", argv[i],
           kr == KERN_SUCCESS ? "REACHABLE" : "denied/absent", kr);
    if (p != MACH_PORT_NULL) mach_port_deallocate(mach_task_self(), p);
  }
  return 0;
}
