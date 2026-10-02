"""Exact 4x4 minor certificate over F9 for fig8 output matrix.
Encoding a+b*i as a+3*b (a,b mod3); hence -1=2, i=3, 1+i=4.
"""
import itertools

def add(x,y): return ((x%3+y%3)%3)+3*(((x//3)+(y//3))%3)
def neg(x): return ((-x%3)%3)+3*((-(x//3))%3)
def mul(x,y):
 a,b=x%3,x//3;c,d=y%3,y//3
 return ((a*c-b*d)%3)+3*((a*d+b*c)%3)
def det(A):
 if len(A)==1:return A[0][0]
 z=0
 for j in range(len(A)):
  M=[r[:j]+r[j+1:] for r in A[1:]]; q=mul(A[0][j],det(M)); z=add(z,q if j%2==0 else neg(q))
 return z
t,s=3,4
O=[[1,0,1,0],[1,0,2,0],[0,1,t,0],[0,1,neg(t),0],[1,1,0,1],[1,1,0,2],[1,2,0,s],[1,2,0,neg(s)]]
for k in (1,2,3):
 assert all(any(det([[O[i][j] for j in C] for i in R]) for C in itertools.combinations(range(4),k)) for R in itertools.combinations(range(8),k))
Z=[]
for R in itertools.combinations(range(8),4):
 if not det([[O[i][j] for j in range(4)] for i in R]):Z.append(R)
assert Z==[(0,1,2,3),(4,5,6,7)],Z
print('PASS F9: every <=3 row subset independent; exactly AB and CD 4-row minors vanish')
