"""Explore the ternary coefficient support; optionally compare an OEIS b-file."""
import argparse
import json, time
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bfile', type=Path, help='Optional OEIS index/value table')
args=parser.parse_args()
start=time.monotonic()
def mul(a,b,n,mod):
 c=[0]*(n+1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b[:n+1-i]):
    if y: c[i+j]+=x*y
 return [x%mod for x in c] if mod else c
def power(a,k,n,mod):
 b=[1]+[0]*n
 while k:
  if k&1:b=mul(b,a,n,mod)
  k//=2
  if k:a=mul(a,a,n,mod)
 return b
def recurrence(N,mod):
 a=[1,1]
 for n in range(2,N+1):
  p=a+[0]
  q=power(p,n+1,n,mod)
  value=n*mul(q,p,n,mod)[n]-(n+1)*q[n]
  a.append(value%mod if mod else value)
 return a
N=400
a=recurrence(N,3)
exact=recurrence(17,None)
s=[0]*(N+1)
powers=[]
k=0
while (3**k-1)//2<=N:
 s[(3**k-1)//2]=1
 powers.append(3**k)
 k+=1
expand=[s[n//3] if n%3==0 else 0 for n in range(N+1)]
r=[1,1]+[0]*(N-1)
sq=mul(expand,expand,N,3)
for n in range(3,N+1):r[n]=(r[n]+2*sq[n-3])%3
pair=[n for n in range(2,201) if any(2*n==3*(u+v) for i,u in enumerate(powers) for v in powers[i+1:])]
power_support=[n for n in range(2,201) if n in powers]
bfile=None
if args.bfile is not None:
 bfile=[]
 for line in args.bfile.read_text().splitlines():
  if line and not line.startswith('#'):
   words=line.split()
   if len(words)==2 and words[0].isdigit():bfile.append(int(words[1]))
result={'exact_prefix_18':exact,'power_support_2_200':power_support,'pair_support_2_200':pair,'zero_count_2_200':sum(x==0 for x in a[2:201]),'iff_mismatches_2_200':[n for n in range(2,201) if ((a[n]==2)!=(n in power_support) or (a[n]==1)!=(n in pair))],'S_equation_mismatches_0_400':[n for n in range(N+1) if s[n] != ((1 if n==0 else 0)+(expand[n-1] if n else 0))%3], 'R_recurrence_mismatches_0_400':[n for n in range(N+1) if r[n]!=a[n]],'elapsed_seconds':time.monotonic()-start}
if bfile is not None:result['oeis_bfile_prefix_matches']=exact==bfile[:18]
print(json.dumps(result,indent=2))
