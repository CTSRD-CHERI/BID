#include <time.h>
#include <stdio.h>

unsigned long long sysTime ()
{
  return time(NULL);
}

void printIPC (unsigned long long insts, unsigned long long cycles)
{
  printf("IPC: %f\n", (double) insts/cycles);
}
