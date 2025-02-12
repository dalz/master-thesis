#include <stdlib.h>

int P;
int *t;

int
chk(int x, int y)
{
        int i;
        int r;

        for (r=i=0; i<4; i++) {
                r = r + t[x + 4*i];
                r = r + t[i + 4*y];
                if (x+i < 4 & y+i < 4)
                        r = r + t[x+i + 4*(y+i)];
                if (x+i < 4 & y-i >= 0)
                        r = r + t[x+i + 4*(y-i)];
                if (x-i >= 0 & y+i < 4)
                        r = r + t[x-i + 4*(y+i)];
                if (x-i >= 0 & y-i >= 0)
                        r = r + t[x-i + 4*(y-i)];
        }
        return r;
}

int
go(int n, int x, int y)
{
        if (n == 4) {
                P++;
                return 0;
        }
        for (; y<4; y++) {
                for (; x<4; x++)
                        if (chk(x, y) == 0) {
                                t[x + 4*y]++;
                                go(n+1, x, y);
                                t[x + 4*y]--;
                        }
                x = 0;
        }
	return 0;
}

int
main()
{
        t = calloc(64, sizeof(int));
        go(0, 0, 0);
        if(P != 92)
        	return 1;
        return 0;
}

