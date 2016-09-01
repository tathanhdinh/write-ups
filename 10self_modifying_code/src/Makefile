all: klein klein32

klein: klein.asm klein_staged.asm klein_staged_n.asm klein_main.cpp
	g++ -c -Os -std=c++11 -fomit-frame-pointer klein_main.cpp
	nasm -felf64 klein.asm
	nasm -felf64 klein_staged.asm
	nasm -felf64 klein_staged_n.asm
	nasm -felf64 klein_staged_n1.asm
	nasm -felf64 klein_staged_n2.asm
	g++ klein.o klein_main.o -o klein_simple
	g++ klein_staged.o klein_main.o -o klein_staged0
	g++ klein_staged_n.o klein_main.o -o klein_staged1
	g++ klein_staged_n1.o klein_main.o -o klein_staged2
	g++ klein_staged_n2.o klein_main.o -o klein_staged3

klein32: klein32_main.cpp klein32.asm klein32_staged0.asm klein32_staged1.asm klein32_staged2.asm klein32_staged3.asm
	g++ -m32 -c -Os -std=c++11 -fomit-frame-pointer klein32_main.cpp -o klein32_main.o
	nasm -felf32 klein32.asm
	nasm -felf32 klein32_staged0.asm
	nasm -felf32 klein32_staged1.asm
	nasm -felf32 klein32_staged2.asm
	nasm -felf32 klein32_staged3.asm
	g++ -m32 klein32_main.o klein32_staged3.o -o klein32

clean:
	rm -f *.o
	rm -f klein_simple klein_staged0 klein_staged1 klein_staged2 klein_staged3 klein32

