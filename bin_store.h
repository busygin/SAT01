#ifndef BIN_STORE_H
#define BIN_STORE_H

#include <stdio.h>

inline int read_int(FILE* file){
  int result=0;
  for(int i=0;i<4;++i)
    result += fgetc(file)<<(i<<3);
  return result;
}

inline void write_int(int x,FILE* file){
  for(int i=0;i<4;++i){
    fputc(x&0xFF,file);
    x>>=8;
  }
}

#endif
