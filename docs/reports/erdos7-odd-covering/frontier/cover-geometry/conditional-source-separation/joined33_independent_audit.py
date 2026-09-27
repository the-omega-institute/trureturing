#!/usr/bin/env python3
"""Independent checks of joined33 results; no optimizer or production separator.

Audit commitment: fail on any selected-token/fee disagreement, missing literal
layout value, incorrect all-domain outer maximum, or mismatched common-field
projection. Exact ordinary finite checks only; no Lean claim. The tiny controls
exhaust all distinct indicator choices, including empty indicators, for central
labels and evaluate every numerical root choice without dominance pruning.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
from math import prod, lcm
from hashlib import sha256
import argparse, importlib.util, json, sys, time
import numpy as np

BASE=Path(__file__).resolve().parent
SEPARATOR=Path(__file__).resolve().with_name('joined33_separator.py')
P=(3,5,7,11,13,17,19); Q=P[2:]
D=(3,5,9,15,25,45,75,225)
COMPOSITES=tuple(p*q for p,q in combinations(P,2) if (p,q)!=(3,5))
LABELS=tuple(sorted(set(D)|set(Q)|set(COMPOSITES)))
PAIRS=set(combinations(D,2))
for p,q in combinations(P,2):
    if (p,q)!=(3,5):
        PAIRS.update(tuple(sorted(z)) for z in ((p,q),(p,p*q),(q,p*q)))
TOKENS=[('unary',d,3,d) for d in LABELS]+[('pair',pair,2,lcm(*pair)) for pair in sorted(PAIRS)]
CHECKS=0

def ck(condition,label):
    global CHECKS
    CHECKS+=1
    if not condition: raise AssertionError(label)

def exact_int_array(x):
    return np.array(x,dtype=object)

def read_common(path):
    data=json.loads(path.read_text()); den=int(data['denominator'])
    points=[tuple(z) for z in data['central']['points']]
    weights=list(map(int,data['central']['weights']))
    unary={p:list(map(int,data['unary'][str(p)])) for p in P}
    pairs={(p,q):exact_int_array(data['pairs'][f'{p},{q}']) for p,q in combinations(P,2)}
    return data,den,points,weights,unary,pairs

def phase_mass(d,phase,points,weights,unary,pairs):
    if d in D:
        return sum(w for (x,y),w in zip(points,weights)
                   if (x+9*(((y-x)*pow(9,-1,25))%25))%d==phase)
    if d in Q:return unary[d][phase]
    p,q=next((p,q) for p,q in combinations(P,2) if p*q==d)
    return int(pairs[p,q][phase%p,phase%q])

def pair_mass(d,e,a,b,points,weights,unary,pairs):
    if d in D and e in D:
        return sum(w for (x,y),w in zip(points,weights)
                   if (x+9*(((y-x)*pow(9,-1,25))%25))%d==a
                   and (x+9*(((y-x)*pow(9,-1,25))%25))%e==b)
    p,q=next((p,q) for p,q in combinations(P,2)
             if {d,e}<={p,q,p*q})
    return sum(int(pairs[p,q][u,v]) for u,v in product(range(p),range(q))
               if (u+p*(((v-u)*pow(p,-1,q))%q))%d==a
               and (u+p*(((v-u)*pow(p,-1,q))%q))%e==b)

def edge_literal_table(p,q,m):
    """Enumerate composite phase indicators, score each triangle literally."""
    out=np.empty((p,q),dtype=object)
    for a,b in product(range(p),range(q)):
        candidates=[]
        for residue in range(p*q):
            u,v=residue%p,residue%q
            value=3*int(m[u,v])
            value+=2*int(m[a,b])
            value+=2*sum(int(m[x,y]) for x,y in [(u,v)] if x==a)
            value+=2*sum(int(m[x,y]) for x,y in [(u,v)] if y==b)
            candidates.append(value)
        out[a,b]=max(candidates)
    return out

def audit_result(input_path,result_path):
    start=time.perf_counter()
    data,den,points,weights,unary,pairs=read_common(input_path)
    result=json.loads(result_path.read_text()); total=sum(weights)
    ck(result['input_sha256']==sha256(input_path.read_bytes()).hexdigest(),'result belongs to this one input')
    layout={int(k):v for k,v in result['layout'].items()}
    ck(set(layout)==set(LABELS) and all(type(v) is int and 0<=v<d for d,v in layout.items()),'all33 literal independent legal choices')
    actual_tokens={(kind,tuple(label) if isinstance(label,list) else label,coeff,modulus)
                   for kind,label,coeff,modulus in result['token_ledger']}
    ck(actual_tokens==set(TOKENS),'independently reconstructed factor ownership')
    ck(len(TOKENS)==121 and sum(z[2] for z in TOKENS)==275,'275 coefficient count')
    literal=sum(3*phase_mass(d,layout[d],points,weights,unary,pairs) for d in LABELS)
    literal+=sum(2*pair_mass(d,e,layout[d],layout[e],points,weights,unary,pairs) for d,e in PAIRS)
    ck(literal==int(result['integer_value']),'all121 selected literal factors attain returned value')
    C=exact_int_array([[int(F(z)*den) for z in row] for row in result['conditional_C']])
    conditional_rows=result.get('conditional_layouts',[])
    ck(len(conditional_rows)==15,'all15 conditional witness rows supplied')
    for row in conditional_rows:
        a,b=row['roots']; lo={int(d):r for d,r in row['layout'].items()}
        ck(set(lo)==set(D) and lo[3]==a and lo[5]==b,'all15 central layout domains')
        score=0
        for (x,y),w in zip(points,weights):
            z=x+9*(((y-x)*pow(9,-1,25))%25)
            hits=[z%d==lo[d] for d in D]
            score+=w*(3*sum(hits)+2*sum(hits[i]*hits[j] for i,j in combinations(range(8),2)))
        ck(score==C[a,b],'all15 central layout scores')
    edge={(p,q):edge_literal_table(p,q,m) for (p,q),m in pairs.items() if (p,q)!=(3,5)}
    # This scan covers the entire original7-root domain. It makes no use of
    # implementation signatures, dominance witnesses or reduced domains.
    dtype=np.int64 if 275*total<2**63 else object
    C=np.array(C,dtype=dtype);edge={key:np.array(v,dtype=dtype) for key,v in edge.items()}
    u={p:np.array(v,dtype=dtype) for p,v in unary.items()}
    count=prod(P); maximum=-1; winning=None; attained=0
    for startcode in range(0,count,32768):
        codes=np.arange(startcode,min(startcode+32768,count),dtype=np.int64)
        rem=codes.copy(); roots={}
        for p in reversed(P): roots[p]=rem%p; rem//=p
        values=C[roots[3],roots[5]].copy()
        for p in Q:values+=3*u[p][roots[p]]
        for (p,q),table in edge.items():values+=table[roots[p],roots[q]]
        local=int(max(values));where=np.flatnonzero(values==local)
        if local>maximum:maximum=local;winning=int(codes[int(where[0])]);attained=len(where)
        elif local==maximum:attained+=len(where)
    ck(maximum==literal,'exhaustive unpruned all7-root maximum')
    # Every reported deletion is independently checked against the complete
    # family of incident conditional energies. The scan above separately checks
    # the semantic consequence, including chains through removed dominators.
    for removed in result['domain_dominance']:
        p,a,b=removed['prime'],removed['removed'],removed['dominator']
        tests=[]
        if p in Q:tests.append((3*u[p][a],3*u[p][b]))
        if p==3:tests.extend(zip(C[a,:],C[b,:]))
        if p==5:tests.extend(zip(C[:,a],C[:,b]))
        for (q,r),table in edge.items():
            if p==q:tests.extend(zip(table[a,:],table[b,:]))
            if p==r:tests.extend(zip(table[:,a],table[:,b]))
        ck(all(y>=x for x,y in tests),'every deleted response has claimed componentwise dominator')
        ck(any(y>x for x,y in tests) or b<a,'acyclic strict/equal dominance direction')
    # Independently read the canonical old query ledger. The selected lcm
    # counts determine the fee; no selection formula is copied from producer.
    W=list(map(F,json.loads((BASE/'actual_pair_activation_certificate.json').read_text())['complete_coefficients']['weighted_nonunit_query']))
    coeff=list(map(F,json.loads((BASE/'remaining33_global_root_exclusion_certificate.json').read_text())['combined512_coefficients']))
    c=F(1084133,201247200);g=1-c
    for i,q in enumerate(Q):
        if i:coeff[256+(1<<i)]+=g/F(q*(q-2))
    selected={};by_lcm=Counter()
    for kind,label,mult,modulus in TOKENS:by_lcm[modulus]+=mult
    for d,mult in by_lcm.items():
        n=d;e3=e5=T=0
        while n%3==0:e3+=1;n//=3
        while n%5==0:e5+=1;n//=5
        normal=F(1)
        for i,q in enumerate(Q):
            if n%q==0:T|=1<<i;n//=q;normal/=q-1
        ck(n==1,'selected modulus screen address')
        selected[32*(4*e3+e5)+T]=mult*normal
    reported={r['screen']:r for r in result['fee_audit']}
    ck(set(reported)==set(selected) and len(selected)==33,'exact selected screen domains')
    for j in range(512):
        pick=selected.get(j,F(0));loss=coeff[j]-c*W[j]
        ck(loss>=0 and W[j]>=pick,'original loss and unselected allheight remainder nonnegative')
        if j in selected:
            r=reported[j]
            ck(F(r['selected_W'])==pick and F(r['old_W'])==W[j]
               and F(r['new_C'])==coeff[j]-c*pick and F(r['unchanged_loss'])==loss
               and F(r['remaining_W'])==W[j]-pick,'every fee split exact against canonical original ledger')
    outside_atoms=[]
    for kind,label,coefficient,modulus in TOKENS:
        is_central=(label in D) if kind=='unary' else all(d in D for d in label)
        if is_central:continue
        upper=max(phase_mass(modulus,r,points,weights,unary,pairs) for r in range(modulus))
        value=(phase_mass(label,layout[label],points,weights,unary,pairs) if kind=='unary' else
               pair_mass(*label,layout[label[0]],layout[label[1]],points,weights,unary,pairs))
        ck(value<=upper,'every outside literal atom bounded by its own marginal maximum')
        outside_atoms.append({'kind':kind,'labels':[label] if kind=='unary' else list(label),
                              'weight':coefficient,'value':str(F(value,den)),'maximum':str(F(upper,den))})
    ck(len(outside_atoms)==85,'exact85 outside atoms')
    Bout=sum(atom['weight']*F(atom['maximum']) for atom in outside_atoms)
    Kcentral=F(max(map(int,C.flat)),den)
    selected_central=F(int(C[layout[3],layout[5]]),den)
    matches=sum(atom['value']==atom['maximum'] for atom in outside_atoms)
    saving=Kcentral+Bout-F(maximum,den)
    ck(saving>=0,'central maximum plus independent outside atoms is upper')
    if matches==85 and selected_central==Kcentral:
        ck(saving==0,'all85 outside maxima and central maximum attained by one literal layout')
    out={'input':str(input_path),'result':str(result_path),'root_tuples_exhausted':count,
         'unpruned_maximizers':int(attained),'value':str(F(maximum,den)),
         'literal_factors':121,'selected_screens':33,'arithmetic':'int64' if dtype is np.int64 else 'arbitrary_integer',
         'conditional_layouts_verified':len(conditional_rows),
         'conditional_maximum_scope':'Returned literal rows verified; central optimality relies on Report392 plus independent tiny exhaustive controls.',
         'source_scope':'Input provenance separately audited from explicit field; pair marginal consistency alone is insufficient.'}
    out['outside_matching']={'outside_atoms':outside_atoms,'outside_atom_count':85,
                             'outside_atoms_at_own_maximum':matches,'outside_atomic_upper':str(Bout),
                             'central_upper':str(Kcentral),'selected_central_value':str(selected_central),
                             'extra_sharing_saving_beyond_central':str(saving)}
    if 'original_screen_values' in data:
        S=list(map(F,data['original_screen_values']))
        ck(list(map(F,data['original_coefficients']))==coeff,'all512 original fee coefficients')
        old=g*F(total,den)-sum(x*y for x,y in zip(coeff,S))
        ck(old==F(data['old_gate']),'original unmodified gate')
        envelope=F(0)
        for j,pick in selected.items():
            mode,T=divmod(j,32);e3,e5=divmod(mode,4)
            d=3**e3*5**e5*prod(q for i,q in enumerate(Q) if T&(1<<i))
            M=max(phase_mass(d,r,points,weights,unary,pairs) for r in range(d))
            normalized=S[j]/prod(q-1 for i,q in enumerate(Q) if T&(1<<i))
            ck(F(M,den)<=normalized,'actual shallow maximum dominated by same-field normalized original screen')
            envelope+=by_lcm[d]*F(M,den)
        paid=sum(pick*S[j] for j,pick in selected.items())
        ck(paid==F(data['selected_joined_screen_fee']),'complete selected same-field screen fee')
        ck(F(maximum,den)<=envelope<=paid,'sharing gain and original envelope directions')
        gate=old+c*(paid-F(maximum,den))
        ck(gate==F(result['joined_gate']),'whole joined gate reconstruction')
        out.update({'old_gate':str(old),'actual_factorwise_envelope':str(envelope),
                    'selected_original_screen_fee':str(paid),'joined_gate':str(gate),'joined_gate_decimal':float(gate)})
    out['seconds']=time.perf_counter()-start
    return out

def tiny_controls():
    spec=importlib.util.spec_from_file_location('audited_separator',SEPARATOR)
    primary=importlib.util.module_from_spec(spec);sys.modules[spec.name]=primary;spec.loader.exec_module(primary)
    cases=[([0,1],[2,3]),([7,232],[1,4]),([0,225,450],[0,2,5])]
    outputs=[]
    for values,weights in cases:
        central={}
        for z,w in zip(values,weights):central[z%225]=central.get(z%225,0)+w
        points=[(z%9,z%25) for z in central];cw=list(central.values())
        unary=[[sum(w for z,w in zip(values,weights) if z%p==a) for a in range(p)] for p in P]
        pairs={(i,j):np.array([[sum(w for z,w in zip(values,weights) if z%P[i]==a and z%P[j]==b)
                               for b in range(P[j])] for a in range(P[i])],dtype=object)
               for i,j in combinations(range(7),2)}
        output=primary.joined_separator(points,cw,[np.array(z,dtype=object) for z in unary],pairs)
        C=np.zeros((3,5),dtype=object); central_choices=0
        # Exhaust distinct support indicators, retaining one empty phase too.
        options={}
        for d in D:
            phases=sorted({z%d for z in values});empty=next((a for a in range(d) if a not in phases),None)
            options[d]=phases+([] if empty is None else [empty])
        for a,b in product(range(3),range(5)):
            best=-1
            for free in product(*(options[d] for d in D if d not in (3,5))):
                layout={3:a,5:b,**dict(zip((d for d in D if d not in (3,5)),free))}
                val=sum(w*(3*sum(z%d==layout[d] for d in D)
                           +2*sum((z%d==layout[d])*(z%e==layout[e]) for d,e in combinations(D,2)))
                        for z,w in zip(values,weights))
                best=max(best,val);central_choices+=1
            C[a,b]=best
        ck([[int(z) for z in row] for row in C]==[[int(F(z)) for z in row] for row in output['conditional_C']],
           'tiny central exhaustive free-label controls, including empty indicators')
        # Enumerate all distinct7-root indicator vectors, including empty,
        # and brute each independent composite's full actual numerical phase.
        rootopts=[]
        for p in P:
            observed=sorted({z%p for z in values});rootopts.append(observed+[next(a for a in range(p) if a not in observed)])
        edge={(P[i],P[j]):edge_literal_table(P[i],P[j],table)
              for (i,j),table in pairs.items() if (i,j)!=(0,1)}
        maximum=-1
        for roots in product(*rootopts):
            r=dict(zip(P,roots));score=int(C[r[3],r[5]])+3*sum(unary[i][roots[i]] for i in range(2,7))
            score+=sum(int(table[r[p],r[q]]) for (p,q),table in edge.items())
            maximum=max(maximum,score)
        ck(maximum==output['integer_value'],'tiny full selected-block control')
        outputs.append({'physical_atoms':values,'integer_weights':weights,'central_layouts_exhausted':central_choices,
                        'distinct_root_indicator_tuples':prod(map(len,rootopts)),'maximum':maximum})
    # Exercise zero measure and arbitrary integer paths on the actual oracle.
    big=10**30
    vals=[0,1];weights=[2*big,3*big]
    unary=[[sum(w for z,w in zip(vals,weights) if z%p==a) for a in range(p)] for p in P]
    pairs={(i,j):np.array([[sum(w for z,w in zip(vals,weights) if z%P[i]==a and z%P[j]==b) for b in range(P[j])] for a in range(P[i])],dtype=object) for i,j in combinations(range(7),2)}
    out=primary.joined_separator([(0,0),(1,1)],weights,[np.array(z,dtype=object) for z in unary],pairs)
    ck(out['integer_value']==outputs[0]['maximum']*big and out['arithmetic']=='arbitrary_integer','arbitrary integer joined homogeneity')
    zero=primary.joined_separator([],[],[np.zeros(p,dtype=object) for p in P],{(i,j):np.zeros((P[i],P[j]),dtype=object) for i,j in combinations(range(7),2)})
    ck(zero['integer_value']==0 and len(zero['layout'])==33,'zero measure empty-source completion')
    return outputs

def main():
    global BASE,SEPARATOR
    ap=argparse.ArgumentParser();ap.add_argument('--pair',nargs=2,action='append',default=[])
    ap.add_argument('--base',type=Path,default=BASE.parent);ap.add_argument('--separator',type=Path,default=SEPARATOR)
    ap.add_argument('--controls',action='store_true');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();BASE=a.base;SEPARATOR=a.separator
    ck(len(LABELS)==33 and len(PAIRS)==88,'independent selected graph size')
    result={'status':'PASS','scope':'Exact finite implementation audit; no source optimization or unrestricted theorem.',
            'producer_family':'GPT-6 same-family independent reader/auditor; not diverse-model review',
            'controls':tiny_controls() if a.controls else [],
            'results':[audit_result(Path(x),Path(y)) for x,y in a.pair],
            'checks':CHECKS,'no_lean':True}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
