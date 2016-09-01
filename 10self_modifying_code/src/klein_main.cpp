// compile with:
//  g++ -c -Os -std=c++11 -fomit-frame-pointer klein_main.cpp
// link with:
//  

#include <cstdio>
#include <string>
#include <cstdint>

extern "C" void insertion(unsigned int, int64_t*);

auto main(int argc, char* argv[]) -> int
{
  if (argc > 1) {
    auto buf = new int64_t[argc - 1];
    unsigned int i = 0;
    for (; i < argc - 1; ++i) buf[i] = atoi(argv[i + 1]);

    insertion(argc - 1, buf);

    for (i = 0; i < argc - 1; ++i) {
      printf("%d ", buf[i]);
    }

    delete[] buf;
  }

  return 0;
}
