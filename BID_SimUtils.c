// 2018, Alexandre Joannou, University of Cambridge
#include <time.h>
#include <stdio.h>

// get system time
unsigned long long sysTime ()
{
  return time(NULL);
}

// print IPC
void printIPC (unsigned long long insts, unsigned long long cycles)
{
  printf("IPC: %f\n", (double) insts/cycles);
}
