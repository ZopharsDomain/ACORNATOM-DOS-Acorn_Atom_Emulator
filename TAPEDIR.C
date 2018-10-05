/*
 * tapedir.c
 * A utility to list the contents of an Atom Emulator .tap file
 * Magnus Olsson, December, 1997
 */

#include <stdio.h>
#include <string.h>

typedef unsigned short WORD;

void readdir(FILE* f)
{
    char name[17];
    int i;
    int c;
    WORD start;
    WORD entry;
    WORD len;

    while (1) {
	for (i = 0; i < 16; ++i) {
	    c = fgetc(f);
	    if (c < 0)
		return; /* End of file */
	    name[i] = c > 0 ? c : ' ';
	}
	name[16] = 0;

	if (fread(&start, sizeof(start), 1, f) != 1)
	    return;
	if (fread(&entry, sizeof(entry), 1, f) != 1)
	    return;
	if (fread(&len, sizeof(len), 1, f) != 1)
	    return;

	printf("%s %04X %04X %04X\n", name, start, entry, len);

	fseek(f, (long) len, SEEK_CUR);
    }
}

void main(int argc, char** argv)
{
    FILE* f;
    char fname[256];

    if (argc != 2) {
	fprintf(stderr, "Usage: tapedir file[.tap]\n");
	exit(0);
    }

    strcpy(fname, argv[1]);
    if (strstr(fname, ".tap") != fname + strlen(fname) - 4)
	strcat(fname, ".tap");

    f = fopen(fname, "rb");
    if (f == NULL) {
	fprintf(stderr, "Couldn't open file %s.\n", fname);
	exit(1);
    }

    readdir(f);
    fclose(f);
}