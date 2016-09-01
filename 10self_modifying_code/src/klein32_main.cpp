// compile with:
//  g++ -m32 -c -Os -std=c++11 -fomit-frame-pointer klein32_main.cpp
// link with:
//  

#include <cstdio>
#include <string>
#include <cstdint>

extern "C" void insertion(uint32_t, uint32_t*);

auto main(int argc, char* argv[]) -> int
{
  if (argc > 1) {
    auto buf = new uint32_t [argc - 1];
    uint32_t i = 0;
    for (; i < argc - 1; ++i) buf[i] = atoi(argv[i + 1]);

    insertion(argc - 1, buf);

    for (i = 0; i < argc - 1; ++i) {
      printf("%d ", buf[i]);
    }

    delete[] buf;
  }

  return 0;
}
