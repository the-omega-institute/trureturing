#!/usr/bin/env python3
"""Finite control for a count summary versus a phase/history read task."""
from fractions import Fraction
from functools import lru_cache
from math import gcd,lcm
import json

def require(ok,msg):
 if not ok: raise RuntimeError(msg)

def data(moduli,phases):
 edges=tuple((i,j) for i in range(len(moduli)) for j in range(i+1,len(moduli))
             if (phases[i]-phases[j])%gcd(moduli[i],moduli[j])==0)
 @lru_cache(None)
 def dp(active,d):
  if not active:return Fraction(1,d)
  v,*rest=active
  neighbors=tuple(i for i in rest if tuple(sorted((i,v))) in edges)
  return dp(tuple(rest),d)-dp(neighbors,lcm(d,moduli[v]))
 value=dp(tuple(range(len(moduli))),1)
 L=lcm(*moduli)
 survivors=tuple(x for x in range(L) if all(x%m!=a for m,a in zip(moduli,phases)))
 require(value==Fraction(len(survivors),L),'exact DP agrees with original residues')
 return edges,value,survivors,dp

def main():
    m=(3,5,15);a=(0,0,1)
    edges,value,survivors,dp=data(m,a)
    # Literal reachable recursion histories: include3/include5 versus skip3/skip5/include15.
    def history(decisions):
     active=tuple(range(len(m)));chosen=[];trace=[];d=1
     for take in decisions:
      require(bool(active),'one decision per active call')
      v,*rest=active
      trace.append((m[v],take))
      if take:
       chosen.append(v);d=lcm(d,m[v])
       active=tuple(i for i in rest if tuple(sorted((i,v))) in edges)
      else:active=tuple(rest)
     require(not active,'both controls reach terminal states')
     original_cell=tuple(x for x in range(15) if all(x%m[i]==a[i] for i in chosen))
     return active,d,chosen,trace,original_cell
    h0=history((True,True));h1=history((False,False,True))
    require(h0[:2]==h1[:2]==((),15),'same old DP key')
    require(dp(h0[0],h0[1])==dp(h1[0],h1[1])==Fraction(1,15),'same old task value')
    require(h0[4]==(0,) and h1[4]==(1,),'distinct original CRT cells')
    require(h0[3][0][1] != h1[3][0][1],'one archived decision bit separates')

    # A separate fixed-family control shows that adding the CRT residue does not
    # recover all history bits. No phase changes inside either branch.
    m0=(3,5,15);a0=(0,0,0)
    g_archive,v_archive,_,_=data(m0,a0)
    def zero_history(decisions):
     active=tuple(range(3));chosen=[];trace=[];d=1
     for take in decisions:
      require(bool(active),'zero-family decision is reachable')
      v,*rest=active;trace.append((m0[v],take))
      if take:
       chosen.append(v);d=lcm(d,m0[v])
       active=tuple(i for i in rest if tuple(sorted((i,v))) in g_archive)
      else:active=tuple(rest)
     require(not active,'zero-family histories are terminal')
     cell=tuple(x for x in range(15) if all(x%m0[i]==a0[i] for i in chosen))
     return active,d,chosen,trace,cell
    z0=zero_history((True,True,False));z1=zero_history((False,False,True))
    require(z0[:2]==z1[:2]==((),15) and z0[4]==z1[4]==(0,),
            'same A,d and original CRT residue')
    require(z0[3][0][1] != z1[3][0][1], 'archive remains distinct after adjoining r')

    # All original phases and the tested residue are transported by one fixed translation.
    p=(0,0,0);p_prime=(1,1,1)
    g0,v0,s0,_=data(m,p);g1,v1,s1,_=data(m,p_prime)
    require(g0==g1 and v0==v1==Fraction(8,15),'same graph and complete count task')
    def covered(x,phases):return any(x%mod==phase for mod,phase in zip(m,phases))
    require(all(covered(x,p)==covered((x+1)%15,p_prime) for x in range(15)),
            'common translation transports every event and the point')
    require(covered(0,p) and not covered(0,p_prime),
            'changing phases while keeping the original point is a different query')
    require(s1==tuple(sorted((x+1)%15 for x in s0)),'survivor transport')

    out={'fixed_family':{'moduli':m,'phases':a,'survivor_density':str(value),
     'histories':[h0,h1],'old_DP_key':[[],15],'old_DP_value':'1/15',
     'SelfRead_first_decision':[True,False],'current_CRT_residues':[0,1]},
     'residue_not_archive':{'moduli':m0,'phases':a0,'histories':[z0,z1],
     'same_enriched_key':[[],15,0],'SelfRead_first_decision':[True,False]},
     'translated_families':{'old':p,'new':p_prime,'survivor_density':'8/15',
     'same_graph':g0,'covered_at_original_zero':[covered(0,p),covered(0,p_prime)],
     'original_phase_3_readout':[p[0],p_prime[0]]},
     'scope':'Finite witness that a count-sufficient DP key need not answer archive/source tasks; no covering truth is changed.'}
    print(json.dumps(out,indent=2))


if __name__ == "__main__":
    main()
