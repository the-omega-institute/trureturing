#!/usr/bin/env python3
"""Standalone native prefix-flip verification, Python standard library only.
Run: python3 verifier.py [--emit]
--emit constructs the word from the supplied degree-two factor and verifies it.
"""
import argparse,hashlib,json,math,time
from pathlib import Path

def flip(v,k):return v[:k][::-1]+v[k:]
def canonical(w):
 w=tuple(w);r=w[::-1]
 return min([w[i:]+w[:i]for i in range(len(w))]+[r[i:]+r[:i]for i in range(len(w))])
POPCOUNT=[bin(i).count('1') for i in range(1<<10)]
def rank(v):
 used=0;result=0;n=len(v)
 for i,value in enumerate(v):
  x=value-1;result=result*(n-i)+x-POPCOUNT[used&((1<<x)-1)];used|=1<<x
 return result

def build_factor(factor):
 n=factor['dimension'];removed={};new={};suppliers=set();old_edges=0
 labels=set(range(1,n+1))
 def permutation(v):return len(v)==n and set(v)==labels and all(type(x)is int for x in v)
 def cut(v,w):
  nonlocal old_edges
  assert permutation(v) and permutation(w)
  assert w in(flip(v,n),flip(v,n-1)),('old edge is not a/b',v,w)
  assert v not in removed and w not in removed,('overlapping old cuts',v,w)
  removed[v]=w;removed[w]=v;old_edges+=1
 def join(v,w):
  assert v not in new and w not in new,('overlapping c replacements',v,w)
  assert flip(v,n-2)==w;new[v]=w;new[w]=v
 for x,W0 in factor['full_E_suppliers']:
  W=tuple(W0);assert type(x)is int and x in labels and len(W)==n-1 and set(W)==labels-{x} and all(type(z)is int for z in W)
  s=(x,canonical(W));assert s not in suppliers;suppliers.add(s)
  for j in range(n-1):
   v=W[j:]+W[:j]+(x,);cut(v,flip(v,n-1));join(v,flip(v,n-2))
 for h0 in factor['T_representatives']:
  h=tuple(h0);assert permutation(h)
  for s in[(h[0],canonical(h[1:])),(h[-1],canonical(h[:-1]))]:assert s not in suppliers;suppliers.add(s)
  word=('ac'+'bc'*(n-3))*2;v=h;vertices=[]
  for s in word:
   vertices.append(v);w=flip(v,{'a':n,'b':n-1,'c':n-2}[s])
   if s=='c':join(v,w)
   else:cut(v,w)
   v=w
  assert v==h and len(set(vertices))==len(vertices)
 assert set(new)==set(removed)
 assert all(removed[w]==v for v,w in removed.items())
 assert all(new[w]==v and flip(v,n-2)==w for v,w in new.items())
 return removed,new,{'whole_E':len(factor['full_E_suppliers']),'T':len(factor['T_representatives']),'distinct_reserved_suppliers':len(suppliers),'old_cut_edges':old_edges,'active_vertices':len(new)}

def audit_rejoin(factor,removed,new):
 """Read the actual input paths after undoing the final whole-E switch."""
 n=factor['dimension'];N=math.factorial(n);r=factor['final_E_rejoin'];x,W0=r['added_E_supplier'];W=tuple(W0)
 selected=[(z,canonical(V))for z,V in factor['full_E_suppliers']]
 assert selected.count((x,canonical(W)))==1
 assert all((x,canonical(W))not in[(h[0],canonical(h[1:])),(h[-1],canonical(h[:-1]))]for h in factor['T_representatives'])
 word=r['relation_word'];assert word=='cb'*(n-1)
 v=tuple(r['representative']);assert v[-1]==x and canonical(v[:-1])==canonical(W)
 vertices=[]
 for s in word:vertices.append(v);v=flip(v,n-1 if s=='b'else n-2)
 assert v==vertices[0] and len(set(vertices))==len(word)
 assert vertices==[tuple(v)for v in r['relation_vertices']]
 k=len(vertices);ports={v:i for i,v in enumerate(vertices)};patch=set(vertices);old={};gamma={}
 assert r['present_edge_indices']==list(range(1,k,2))
 for j in range(k):
  v,w=vertices[j],vertices[(j+1)%k]
  if j%2:
   assert flip(v,n-1)==w and removed[v]==w and removed[w]==v
   old[j]=(j+1)%k;old[(j+1)%k]=j
  else:
   assert flip(v,n-2)==w and new[v]==w and new[w]==v
   gamma[j]=j+1;gamma[j+1]=j
 # Undo the added E. Its reserved supplier is unused, so its vertices have
 # both native a/b neighbours in the input and no remaining c replacement.
 def input_neighbors(v):
  if v not in patch and v in new:
   a=flip(v,n);other=flip(v,n-1)if removed[v]==a else a
   return [other,new[v]]
  return [flip(v,n),flip(v,n-1)]
 seen=bytearray(N);beta={};weights={};covered=0;offsets={};oriented={};input_lengths=r['input_circuit_lengths']
 for d in r['outside_beta']:
  i,j=d['ends'];assert i not in beta and j not in beta and i!=j
  start=vertices[i];v=start;prev=None;length=0
  while True:
   rv=rank(v);assert not seen[rv],('overlapping actual rejoin paths',v);seen[rv]=1;covered+=1
   if v!=start and v in ports:break
   neighbors=input_neighbors(v)
   if v in ports:neighbors.remove(vertices[old[ports[v]]])
   choices=[w for w in neighbors if w!=prev];assert len(choices)==1
   prev,v=v,choices[0];length+=1
  assert v==vertices[j] and length==d['length']
  beta[i]=j;beta[j]=i;weights[frozenset((i,j))]=length
  idx=d['original_component'];L=input_lengths[idx];p,q=d['start_offset'],d['end_offset'];assert 0<=p<L and 0<=q<L and(q-p)%L==length
  offsets[i]=(idx,p);offsets[j]=(idx,q);oriented[i]=('out',j);oriented[j]=('in',i)
 assert covered==N and all(seen) and set(beta)==set(range(k))
 # The recorded offsets give a consistent orientation, up to circle rotation.
 for i in range(1,k,2):
  j=(i+1)%k;ci,p=offsets[i];cj,q=offsets[j];assert ci==cj;L=input_lengths[ci]
  if(q-p)%L==1:assert oriented[i][0]=='in'and oriented[j][0]=='out'
  else:assert(p-q)%L==1 and oriented[j][0]=='in'and oriented[i][0]=='out'
 def circuits(matching):
  unseen=set(range(k));result=[]
  while unseen:
   start=min(unseen);v=start;seq=[v];length=0
   while True:
    unseen.discard(v);w=beta[v];unseen.discard(w);length+=weights[frozenset((v,w))]+1;v=matching[w];seq.extend([w,v])
    if v==start:break
   result.append({'length':length,'endpoint_circuit':seq})
  return result
 before=circuits(old);after=circuits(gamma)
 assert sorted(d['length']for d in before)==sorted(input_lengths)
 assert len(after)==1 and after[0]['length']==N and after[0]['endpoint_circuit']==r['endpoint_circuit']
 seq=r['endpoint_circuit'];assert seq[-2:]==[1,0]and flip(vertices[1],n-2)==vertices[0]and r['endpoint_closing_generator']=='c'
 return {'rejoin_actual_paths':len(weights),'rejoin_covered_vertices':covered,'input_circuit_lengths':sorted(input_lengths),'rejoin_endpoint_circuit':seq,'rejoin_endpoint_closing_generator':'c'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--emit',action='store_true');args=p.parse_args();root=Path(__file__).resolve().parent;t0=time.monotonic()
 factor=json.loads((root/'factor.json').read_text());n=factor['dimension'];N=math.factorial(n);start=tuple(factor['start']);assert sorted(start)==list(range(1,n+1))
 removed,new,stats=build_factor(factor);seen=bytearray(N);v=start;prev=None;generated=bytearray()
 word=None if args.emit else (root/'hamilton-n10-word.txt').read_text().strip();assert word is None or len(word)==N
 for j in range(N):
  r=rank(v);assert not seen[r],('repeated vertex',j,v);seen[r]=1
  if args.emit:
   if v in new:
    a=flip(v,n);s='b'if removed[v]==a else'a';neighbors=[(s,flip(v,n if s=='a'else n-1)),('c',new[v])]
   else:neighbors=[('a',flip(v,n)),('b',flip(v,n-1))]
   choices=[(s,w)for s,w in neighbors if w!=prev];assert len(choices)==(2 if j==0 else 1)
   s,w=choices[0];generated.append(ord(s))
  else:
   s=word[j];assert s in'abc';w=flip(v,{'a':n,'b':n-1,'c':n-2}[s])
   assert(new.get(v)==w if s=='c'else removed.get(v)!=w),('edge absent from factor',j,s,v)
  prev,v=v,w
  if j%500000==0:print({'visited':j+1,'elapsed_seconds':round(time.monotonic()-t0,2)},flush=True)
 assert v==start;assert all(seen);assert prev!=start
 if args.emit:
  word=generated.decode();(root/'hamilton-n10-word.txt').write_text(word+'\n')
 digest=hashlib.sha256(word.encode()).hexdigest();expected=factor.get('word_sha256')
 if expected:assert digest==expected
 rejoin=audit_rejoin(factor,removed,new)
 result={'dimension':n,'word_edges':N,'distinct_vertices':N,'returns_to_identity':True,'actual_closing_generator':word[-1],'word_sha256_without_newline':digest,'word_file_sha256':hashlib.sha256((root/'hamilton-n10-word.txt').read_bytes()).hexdigest(),'factor_sha256':hashlib.sha256((root/'factor.json').read_bytes()).hexdigest(),**stats,**rejoin,'elapsed_seconds':round(time.monotonic()-t0,2)}
 if args.emit:(root/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(result,flush=True)
if __name__=='__main__':main()
