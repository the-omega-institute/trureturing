"""Full-height absorption of a larger prime into a smaller prime coordinate.

Exact finite even controls, not an all-odd witness or Lean verification.
The finite complete-period cap is a checker limitation, not a hypothesis of
an arbitrary-period mathematical statement. All file accesses are explicit.
Optional --source reads only the named fresh_root_constructor.py as AST data
for the existing 5040/13440 controls; no imported producer code is executed.
"""
from math import gcd,lcm
from itertools import combinations
from collections import Counter
from pathlib import Path
import ast,json,hashlib,argparse

def req(p,msg):
    if not p: raise ValueError(msg)
def v(n,p):
    h=0
    while n%p==0: h+=1;n//=p
    return h
def factors(n):
    out=[];p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:out.append(n)
    return out
def crt(a,m,b,n):
    req(gcd(m,n)==1,'noncoprime CRT')
    return (a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
def event(C,x):return tuple(int((x-a)%m==0) for a,m in C)
def lattice(C,r,q,filtered=False):
    Q=lcm(*(m for a,m in C));H=v(Q,r);G=v(Q,q);R=r**H;T=q**G;M=Q//R//T
    qfree=[(a,m) for a,m in C if m%q]
    rows=[]
    for u in range(R):
        live=[z for z in range(M) if not any((u-a)%r**v(m,r)==0 and (z-a)%(m//r**v(m,r))==0 for a,m in qfree)]
        low=[]
        for i,(a,m) in enumerate(C):
            h=v(m,r);e=v(m,q);s=m//r**h//q**e
            if e and h<H and (u-a)%r**h==0 and (not filtered or any((z-a)%s==0 for z in live)):
                low.append(i)
        forbidden={z for z in range(T) if any((z-C[i][0])%q**v(C[i][1],q)==0 for i in low)}
        good=[None]*(G+1);good[G]=[z not in forbidden for z in range(T)]
        for e in range(G-1,-1,-1):
            good[e]=[sum(good[e+1][z+d*q**e] for d in range(q))>=r for z in range(q**e)]
        rows.append({'u':u,'live_M':live,'low_labels':low,'forbidden':sorted(forbidden),'good':good})
    return {'Q':Q,'H':H,'G':G,'M':M,'r':r,'q':q,'rows':rows,'passes':all(x['good'][0][0] for x in rows)}
def audit(C,r,q,*,filtered=False,allow_even=False,irredundant=False,max_period=200000):
    C=list(C)
    req(C and all(isinstance(a,int) and isinstance(m,int) and m>1 for a,m in C),'nonunit integer originals')
    C=[(a%m,m) for a,m in C]
    req(lcm(*(m for a,m in C))<=max_period,'finite complete-period cap exceeded')
    req(allow_even or all(m%2 for a,m in C),'even input forbidden')
    req(isinstance(r,int) and isinstance(q,int) and 2<=r<q and factors(r)==[r] and factors(q)==[q],'ordered primes required')
    req(all(lcm(*(m for a,m in C))%p==0 for p in (r,q)),'missing source prime')
    req(len({m for a,m in C})==len(C),'distinct originals')
    L=lattice(C,r,q,filtered);req(L['passes'],'filtered tree premise' if filtered else 'strong tree premise')
    Q,H,G,M=L['Q'],L['H'],L['G'],L['M'];R=r**H;T=q**G;N=r**(H+G)*M
    private=[0]*len(C);witness=[None]*len(C)
    for x in range(Q):
        e=event(C,x);req(any(e),'not whole cover')
        if sum(e)==1:
            i=e.index(1);private[i]+=1
            if witness[i] is None:witness[i]=x
    req(not irredundant or all(private),'original redundancy')
    theta=[]
    for row in L['rows']:
        u=row['u'];layers=[{0:0}]
        for e in range(G):
            layer={}
            for z,old in layers[-1].items():
                start=(u+e+old+1)%q
                digits=[(start+j)%q for j in range(q)]
                selected=[d for d in digits if row['good'][e+1][old+d*q**e]][:r]
                req(len(selected)==r,'incomplete branch')
                for b,d in enumerate(selected):layer[z+b*r**e]=old+d*q**e
            req(len(layer)==r**(e+1) and len(set(layer.values()))==len(layer),'prefix injection')
            layers.append(layer)
        theta.append(layers)
    out=[];mapping={};discarded=[]
    for i,(a,m) in enumerate(C):
        h=v(m,r);e=v(m,q);s=m//r**h//q**e
        if not e: b,n=a,m
        elif h<H:discarded.append(i);continue
        else:
            u=a%R;inv={old:z for z,old in theta[u][e].items()}
            if a%q**e not in inv:discarded.append(i);continue
            n=r**(H+e)*s;b=crt(u+R*inv[a%q**e],r**(H+e),a%s,s)
        mapping[i]=len(out);out.append((b%n,n))
    req(len({m for a,m in out})==len(out),'output modulus collision')
    req(all(m%q for a,m in out),'larger prime remains in output')
    req(N%lcm(*(m for a,m in out))==0,'output period exceeds common carrier')
    req((len(out),sum(m for a,m in out))<(len(C),sum(m for a,m in C)),'no lex descent')
    digest=hashlib.sha256();hist=Counter();oldimages=set();coordinates=0;live_points=0;outside_live_discarded_hits=0;full_vectors_equal=True
    for x in range(N):
        u=x%R;z=(x//R)%r**G
        old=crt(crt(u,R,theta[u][G][z],T),R*T,x%M,M)
        old_e=event(C,old);new_e=event(out,x)
        pulled=tuple(new_e[mapping[i]] if i in mapping else 0 for i in range(len(C)))
        req(all(old_e[i]==pulled[i] for i in mapping),'retained original event mismatch')
        full_vectors_equal=full_vectors_equal and old_e==pulled
        if not filtered:req(old_e==pulled,'full original event vector mismatch')
        req(any(new_e),'output hole')
        live=x%M in L['rows'][u]['live_M']
        if live:
            live_points+=1
            req(all(not old_e[i] for i in discarded),'dropped original hit on live cofactor')
        else:outside_live_discarded_hits+=sum(old_e[i] for i in discarded)
        oldimages.add(old);hist[sum(new_e)]+=1;coordinates+=len(C)
        digest.update(bytes(old_e));digest.update(bytes(new_e))
    req(len(oldimages)==N,'source map not injective')
    output_private=[0]*len(out)
    for x in range(lcm(*(m for a,m in out))):
        e=event(out,x)
        if sum(e)==1:output_private[e.index(1)]+=1
    rows=[{'u':row['u'],'live_M':row['live_M'],'low_labels':row['low_labels'],'forbidden':row['forbidden'],'theta':[[d[z] for z in range(len(d))] for d in theta[row['u']]]} for row in L['rows']]
    return {'r':r,'q':q,'H':H,'G':G,'M':M,'original':C,'original_period':Q,'original_count':len(C),'original_modulus_sum':sum(m for a,m in C),'original_private_counts':private,'original_private_witnesses':witness,'output':out,'output_period':lcm(*(m for a,m in out)),'output_count':len(out),'output_modulus_sum':sum(m for a,m in out),'output_private_counts':output_private,'old_to_new':mapping,'discarded_originals':discarded,'transport_carrier':N,'event_coordinates_checked':coordinates,'retained_event_coordinates_checked':N*len(mapping),'live_transport_points':live_points,'outside_live_discarded_event_hits':outside_live_discarded_hits,'source_map_images':len(oldimages),'event_vector_sha256':digest.hexdigest(),'output_multiplicity_histogram':dict(sorted(hist.items())),'theta_rows':rows,'all_retained_event_vectors_match':True,'all_full_event_vectors_match':full_vectors_equal,'filtered':filtered}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--source');parser.add_argument('--output',required=True);args=parser.parse_args()
    source=ast.parse(Path(args.source).read_text()) if args.source else ast.Module(body=[],type_ignores=[]);seeds={}
    for fn in source.body:
        if isinstance(fn,ast.FunctionDef):
            name='original5040' if fn.name=='main' else 'classes' if fn.name=='cross_joint_probability_control' else None
            if name:
                for node in fn.body:
                    if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in node.targets):seeds[name]=ast.literal_eval(node.value);break
    tests=[]
    for name,C in seeds.items():
        Q=lcm(*(m for a,m in C));req(all(any(event(C,x)) for x in range(Q)),'seed not cover')
        for r,q in combinations(factors(Q),2):
            row={'seed':name,'r':r,'q':q,'period':Q}
            for filtered in (False,True):
                L=lattice(C,r,q,filtered);bad=[x for x in L['rows'] if not x['good'][0][0]]
                row['filtered' if filtered else 'strong']={'passes':L['passes'],'bad_u_count':len(bad),'first_bad_u':None if not bad else bad[0]['u'],'first_bad_live_M':None if not bad else bad[0]['live_M'],'first_bad_forbidden':None if not bad else bad[0]['forbidden']}
            tests.append(row)
    # A nonredundant inverse construction of the classical period-12 cover
    # embedded in the unique u=7 fibre; no redundant labels are added.
    C=[(0,2),(1,4),(3,8),(23,40),(7,24),(119,200),(119,120),(399,600),(0,5),(1,10),(7,20),(4,25),(9,50),(39,100)]
    positive=audit(C,2,5,allow_even=True,irredundant=True)
    strict=C+[(13,15)]
    strong=lattice(strict,2,5)
    req(not strong['passes'],'strict filtering control unexpectedly satisfies strong premise')
    filtered=audit(strict,2,5,filtered=True,allow_even=True)
    req(filtered['original_private_counts'][-1]==0,'new filtering-only label is not redundant')
    req(filtered['output']==positive['output'],'filtering control changes retained output')
    req(not filtered['all_full_event_vectors_match'] and filtered['outside_live_discarded_event_hits']>0,'filtered control does not separate full from retained events')
    negative=[]
    for label,bad,r,q,opts,expected in [
        ('even-not-authorized',C,2,5,{},'even input forbidden'),
        ('removed-needed-label',C[:-1],2,5,{'allow_even':True},'not whole cover'),
        ('repeated-original-modulus',C+[(1,2)],2,5,{'allow_even':True},'distinct originals'),
        ('reversed-primes',C,5,2,{'allow_even':True},'ordered primes required'),
        ('absent-source-prime',C,2,7,{'allow_even':True},'missing source prime'),
        ('unfiltered-strict-control',strict,2,5,{'allow_even':True},'strong tree premise')]:
        try:audit(bad,r,q,**opts)
        except ValueError as exc:
            req(expected in str(exc),'incorrect negative-control rejection')
            negative.append({'case':label,'diagnostic':str(exc)})
        else:raise ValueError('invalid negative control admitted')
    report={'fixture_pair_probes':tests,'positive_control':positive,'filtered_control':filtered,'strict_strong_bad_u':[row['u'] for row in strong['rows'] if not row['good'][0][0]],'negative_controls':negative,'scope':'Even whole-cover controls only. The 14-class positive source is irredundant. The 15th class in the strict filtering control is deliberately redundant; it distinguishes the two sufficient premises only. Ordinary finite evidence; no all-odd cover or Lean result.'}
    Path(args.output).write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'positive_input_period':report['positive_control']['original_period'],'output_period':report['positive_control']['output_period'],'original_count':len(C),'output_count':report['positive_control']['output_count'],'fixture_pairs':len(tests)}))
if __name__=='__main__':main()
