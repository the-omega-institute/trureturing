#!/usr/bin/env python3
"""Exact producer for Report594 + original 63, with the 23/29 continuation.

Default: independently generate input, compile/run the adjacent C++ engine,
and write the adjacent JSON. --reuse-run is only a handoff option: it verifies
an unchanged numerical engine and byte-identical historical input, and labels
the resulting evidence as reused, never as a full run of the new wrapper.
Only Python's standard library and a C++17 compiler are required.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import permutations, product
import json
import math
from pathlib import Path
import random
import re
import subprocess
import tempfile

P = (3, 5, 7, 11, 13, 17, 19)
Q = P[2:]
G = F(566, 49)
SCALE = 10**8
D = 1 << 20
SD = 36 * D
THRESHOLD = F(1, 1000)
GAIN = math.floor(G * SCALE)
TRIPLES = ((3,0,2),(3,1,2),(3,2,1),(4,0,2),(4,2,2),(5,1,2),(5,2,2),(6,2,2))
STATES = tuple((r, t if r == 0 else 9-t, u, um) for r in range(2) for t,u,um in TRIPLES)
HISTORICAL_INPUT_SHA256 = 'b1a7b6a0c9d22f53346ef4a324d449317ad423f5de24e31223afd36994087538'
HISTORICAL_ENGINE_SHA256 = '9285734abbcd1ee78f5c28e61a197d212b94df9ab756ecd207269c6a52c09a5e'
HISTORICAL_RUN_SHA256 = '075a7bb71222dada797315591632fd72c4632f2a8e4d566059ff906aac6229e1'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prod(xs):
    return math.prod(xs, start=F(1))


def digest(data):
    return sha256(data).hexdigest()


def fractions_json(obj):
    if isinstance(obj, F):
        return str(obj)
    if isinstance(obj, dict):
        return {str(k): fractions_json(v) for k,v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [fractions_json(v) for v in obj]
    return obj


def coordinate_weight(p):
    return F(3,p-1) + (F(2*p,(p-1)**2)+F(3,p-1))/F(p-2)


def coefficients():
    loss, query, sf_loss, tail_loss, weighted = ([] for _ in range(5))
    for mode in range(8):
        rows = ([],[],[],[],[])
        for mask in range(32):
            other = tuple(q for k,q in enumerate(Q) if mask >> k & 1) + ((5,) if mode & 1 else ())
            full = prod(F(1,p-2) for p in other)
            low = prod(F(1,p-2)-F(1,p*(p-1)*(p-2)) for p in other)
            sf = prod(F(1,p-1) for p in other)
            sf_charge = tail_charge = F(0)
            if mode < 2:
                if len(other) >= 2:
                    tail_charge = full-low
                    if not (len(other) == 2 and 5 in other):
                        sf_charge = sf
                qry = full if other else F(0)
            else:
                if other:
                    if mode < 6:
                        tail_charge = full-low
                        if mode < 4 and len(other) >= 2 and not (len(other) == 2 and 5 in other):
                            sf_charge = sf
                    else:
                        tail_charge = full
                qry = full
            weight = prod(coordinate_weight(p) for p in other)
            if mode < 2:
                weight *= bool(other)
            else:
                weight *= (3,5,8)[(mode-2)//2]
            for row,v in zip(rows, (sf_charge+tail_charge,qry,sf_charge,tail_charge,weight)):
                row.append(v)
        for target,row in zip((loss,query,sf_loss,tail_loss,weighted),rows):
            target.append(row)
    combined = [[G*loss[m][t]+query[m][t] for t in range(32)] for m in range(8)]
    return dict(loss=loss,query=query,sf_loss=sf_loss,tail_loss=tail_loss,weighted=weighted,combined=combined)


COEF = coefficients()
ROUNDED = [[math.ceil(v*SCALE) for v in row] for row in COEF['combined']]
BETA = [prod(1-F(3,q-1)-F(2,q*(q-2)) for q in Q[d:]) for d in range(6)]
BETA_LO = [math.floor(v*D) for v in BETA]


def factor(q, code, alt, cell):
    r,j = divmod(cell,4)
    rr,cc,kr,kc = code//32,(code//8)%4,(code//4)%2,code%4
    v = 1-(F(1,q-1)+F(1,q*(q-2)))*(int(r==rr)+int(j==cc))-F(1,q-1)*int((r,j)==(kr,kc))
    if q == 7 and alt:
        v -= F(1,6)
    require(0 < v <= 1, 'nonpositive or oversized factor')
    return v


FACTORS = [[[[factor(q,c,a,k) for k in range(8)] for a in range(2)] for c in range(64)] for q in Q]
FAC_LO = [[[[math.floor(v*D) for v in row] for row in pair] for pair in q] for q in FACTORS]
FAC_HI = [[[[math.ceil(v*D) for v in row] for row in pair] for pair in q] for q in FACTORS]


def input_text():
    lines = [f'{SCALE} {GAIN} {D} 1000', ' '.join(str(x) for row in ROUNDED for x in row), str(len(STATES))]
    lines += [' '.join(map(str,s)) for s in STATES]
    lines.append(' '.join(map(str,BETA_LO)))
    for qi in range(5):
        for code in range(64):
            for alt in range(2):
                lines.append(' '.join(str(v) for k in range(8) for v in (FAC_LO[qi][code][alt][k], FAC_HI[qi][code][alt][k])))
    return '\n'.join(lines)+'\n'


def vertex_states():
    vertices = sorted(set(permutations((0,1,2,2,2,2))))
    require(len(vertices)==30, 'capped-simplex vertex count')
    representatives = {}
    for w in vertices:
        require(sum(w)==9 and max(w)==2, 'capped simplex')
        for mark in range(6):
            r=mark//3
            key=(r,sum(w[:3]),w[mark],max(w[l] for l in range(3*r,3*r+3) if l!=mark))
            require(key in STATES, 'vertex omitted by sixteen-state reduction')
            require(max(w[l] for l in range(6) if l//3!=r)==2, 'other-root maximum')
            # Choose a representative with the marked leaf first in its row.
            if mark in (0,3):
                representatives.setdefault(STATES.index(key),(tuple(F(v,9) for v in w),mark))
    require(set(representatives)==set(range(16)), 'unreached sufficient state')
    return vertices, representatives


VERTICES, REPRESENTATIVES = vertex_states()


@lru_cache(None)
def suffix_slots(slots, maxname):
    if slots == 0:
        return 1
    return (maxname+1)*suffix_slots(slots-1,maxname)+(suffix_slots(slots-1,maxname+1) if maxname<3 else 0)


def suffix_count(depth,maxname):
    return 4**(5-depth)*suffix_slots(2*(5-depth),maxname)


ORBITS = 2**10*(4**10+3*2**10+2)//6
require(ORBITS==179481600 and suffix_count(0,0)==ORBITS, 'independent Burnside/slot mismatch')
CASES = 16*ORBITS


def validate_prefix(codes):
    maxname=0
    for code in codes:
        require(0 <= code < 64, 'invalid layout code')
        for name in ((code//8)%4, code%4):
            require(name<=min(3,maxname+1), 'noncanonical restricted-growth prefix')
            maxname=max(maxname,name)
    return maxname


def grid(codes,mark,mask):
    out=[]
    for l,j in product(range(6),range(4)):
        val=F(int((l//3,j)!=(0,0)))
        for qi in range(5):
            if not (mask>>qi&1):
                val*=FACTORS[qi][codes[qi]][int(l==mark)][4*(l//3)+j]
        out.append(val)
    return out


def screens(g,w):
    row=[sum(g[4*l:4*l+4])/4 for l in range(6)]
    return (
        sum(w[l]*row[l] for l in range(6)),
        max(sum(w[l]*g[4*l+j] for l in range(6)) for j in range(4)),
        max(sum(w[l]*row[l] for l in range(3*r,3*r+3)) for r in range(2)),
        max(sum(w[l]*g[4*l+j] for l in range(3*r,3*r+3)) for r,j in product(range(2),range(4))),
        max(w[l]*row[l] for l in range(6)),
        max(w[l]*g[4*l+j] for l,j in product(range(6),range(4))),
        max(row)/9,
        max(g)/9,
    )


def exact_modes(codes,w,mark):
    values=[screens(grid(codes,mark,t),w) for t in range(32)]
    result={name:sum(COEF[name][m][t]*values[t][m] for m,t in product(range(8),range(32))) for name in ('sf_loss','tail_loss','query','weighted')}
    result['block']=values[0][0]
    result['mass']=result['block']-result['sf_loss']-result['tail_loss']
    result['gate']=G*result['mass']-result['query']
    direct=G*result['block']-sum(COEF['combined'][m][t]*values[t][m] for m,t in product(range(8),range(32)))
    require(direct==result['gate'], '256-mode gate identity')
    return result


def exact_supports(codes,w,mark):
    """Independent expansion over all 127 supports; does not use mode tables."""
    grids=[grid(codes,mark,t) for t in range(32)]
    block=sum(w[l]*grids[0][4*l+j]/4 for l,j in product(range(6),range(4)))
    sf=tail=query=weighted=F(0)
    for bits in range(1,128):
        support=tuple(p for k,p in enumerate(P) if bits>>k&1)
        other=tuple(p for p in support if p!=3)
        mask=sum(1<<k for k,p in enumerate(Q) if p in support)
        g=grids[mask]
        full=prod(F(1,p-2) for p in other)
        low=prod(F(1,p-2)-F(1,p*(p-1)*(p-2)) for p in other)
        squarefree=prod(F(1,p-1) for p in other)
        weight=prod(coordinate_weight(p) for p in other)
        moved=(len(support)==2 and bool(set(support)&{3,5})) or (3 in support and 5 in support and len(support)==3)
        if 3 not in support:
            if 5 in support:
                v=max(sum(w[l]*g[4*l+j] for l in range(6)) for j in range(4))
            else:
                v=sum(w[l]*g[4*l+j]/4 for l,j in product(range(6),range(4)))
            query+=v*full
            weighted+=v*weight
            if len(support)>=2:
                tail+=v*(full-low)
                if not moved:
                    sf+=v*squarefree
        else:
            if 5 in support:
                first=max(sum(w[l]*g[4*l+j] for l in range(3*r,3*r+3)) for r,j in product(range(2),range(4)))
                second=max(w[l]*g[4*l+j] for l,j in product(range(6),range(4)))
                deep=F(1,9)*max(g[4*l+j] for l,j in product(range(6),range(4)) if w[l]>0)
            else:
                average=[sum(g[4*l:4*l+4])/4 for l in range(6)]
                first=max(sum(w[l]*average[l] for l in range(3*r,3*r+3)) for r in range(2))
                second=max(w[l]*average[l] for l in range(6))
                deep=F(1,9)*max(average[l] for l in range(6) if w[l]>0)
            query+=(first+second+deep)*full
            weighted+=(3*first+5*second+8*deep)*weight
            if len(support)>=2:
                tail+=(first+second)*(full-low)+deep*full
                if not moved:
                    sf+=first*squarefree
    mass=block-sf-tail
    return dict(block=block,sf_loss=sf,tail_loss=tail,mass=mass,query=query,gate=G*mass-query,weighted=weighted)


def integer_bound(codes,sid):
    """Reconstruct any partial branch using exact integer input operations."""
    depth=len(codes)
    require(1<=depth<=5 and 0<=sid<16,'invalid partial branch')
    lo=[[[D if k else 0 for k in range(8)] for _ in range(2)]]
    hi=[[[D if k else 0 for k in range(8)] for _ in range(2)]]
    for qi,code in enumerate(codes):
        lo_new=[]; hi_new=[]
        for t in range(1<<qi):
            lo_new.append([[lo[t][a][k]*FAC_LO[qi][code][a][k]//D for k in range(8)] for a in range(2)])
            hi_new.append([[(hi[t][a][k]*FAC_HI[qi][code][a][k]+D-1)//D for k in range(8)] for a in range(2)])
        lo=lo_new+lo
        hi=hi_new+hi
    mark,t,u,um=STATES[sid]
    mass=0
    for r,j in product(range(2),range(4)):
        k=4*r+j
        mass+=(t if r==0 else 9-t)*lo[0][0][k]
        if r==mark:
            mass+=u*(lo[0][1][k]-lo[0][0][k])
    mass=mass*BETA_LO[depth]//D
    value=GAIN*mass
    for mask in range(1<<depth):
        b,a=hi[mask]
        bs=[sum(b[:4]),sum(b[4:])]
        aa=[sum(a[:4]),sum(a[4:])]
        wa=[(t if r==0 else 9-t)*b[4*r+j]+(u*(a[4*r+j]-b[4*r+j]) if r==mark else 0) for r,j in product(range(2),range(4))]
        rs=[sum(wa[:4]),sum(wa[4:])]
        leaf=max([((um if r==mark else 2)*b[4*r+j]) for r,j in product(range(2),range(4))]+[u*a[4*mark+j] for j in range(4)])
        rowleaf=max([(um if r==mark else 2)*bs[r] for r in range(2)]+[u*aa[mark]])
        v=(sum(rs),4*max(wa[j]+wa[j+4] for j in range(4)),max(rs),4*max(wa),rowleaf,4*leaf,max(bs),4*max(b))
        for mode in range(8):
            collapsed=sum(ROUNDED[mode][m] for m in range(32) if m% (1<<depth)==mask)
            value-=collapsed*v[mode]
    return value


def arithmetic_bounds():
    total=sum(sum(row) for row in ROUNDED)
    signed=(GAIN+total)*SD
    raw=D*D+D-1
    require(signed<2**63 and raw<2**64 and SD*D<2**63, 'unsafe arithmetic')
    # Five rounded factors and four rounded multiplications: <= 9/D.
    # A partial lower mass adds beta rounding and the final floor: <= 11/D.
    coefficient_error=sum(F(ROUNDED[m][t],SCALE)-COEF['combined'][m][t] for m,t in product(range(8),range(32)))
    rounding=F(11*GAIN+9*total,SCALE*D)+(G-F(GAIN,SCALE))+coefficient_error
    require(rounding>0,'rounding envelope')
    return dict(signed64_absolute_accumulation_bound=signed,uint64_product_plus_rounding_bound=raw,mass_beta_product_bound=SD*D,rounded_gain=GAIN,rounded_coefficient_sum=total,product_absolute_error=F(9,D),partial_mass_absolute_error=F(11,D),gate_rounding_error_upper=rounding,gate_rounding_error_upper_decimal=float(rounding))


def parse_run(text):
    lines=text.splitlines()
    require(len(lines)==7,'scan output must have exactly seven lines')
    pattern=r'threshold 1/(\d+) certified (\d+) expected (\d+) failed (\d+) lower (\d+) denominator (\d+) state (\d+) depth (\d+) codes ((?:\d+ ){4}\d+) seconds ([0-9]+(?:\.[0-9]+)?)'
    m=re.fullmatch(pattern,lines[0])
    require(m is not None,'malformed scan header')
    threshold,certified,expected,failed,lower,denominator,sid,depth=map(int,m.groups()[:8])
    codes=tuple(map(int,m.group(9).split()))
    require(threshold==1000 and denominator==SCALE*SD,'threshold or denominator mismatch')
    require(certified==expected==CASES and failed==0,'incomplete or failing scan')
    require(lower>=math.ceil(THRESHOLD*denominator),'certificate below threshold')
    require(0<=sid<16 and 1<=depth<=5,'invalid minimum branch state/depth')
    require(all(0<=c<64 for c in codes),'invalid printed code')
    prefix=codes[:depth]
    maxname=validate_prefix(prefix)
    require(integer_bound(prefix,sid)==lower,'minimum partial-branch reconstruction mismatch')
    counters=[]
    for d,line in enumerate(lines[1:]):
        mm=re.fullmatch(r'(\d+) nodes (\d+) eval (\d+) pruned (\d+)',line)
        require(mm is not None,'malformed depth counter')
        got,nodes,evaluated,pruned=map(int,mm.groups())
        require(got==d and 0<=pruned<=evaluated<=16*nodes,'inconsistent depth counter')
        counters.append(dict(depth=d,nodes=nodes,evaluated=evaluated,pruned=pruned))
    require(counters[0]==dict(depth=0,nodes=1,evaluated=0,pruned=0),'invalid root counter')
    require(counters[5]['evaluated']==counters[5]['pruned'],'uncertified terminal leaf')
    require(counters[5]['nodes']<=ORBITS,'excess terminal layouts')
    require(sum(v['pruned'] for v in counters)<=CASES,'excess pruned states')
    return dict(threshold=THRESHOLD,certified_cases=certified,expected_cases=expected,failed_leaves=failed,minimum_certified_branch_lower=F(lower,denominator),minimum_is_exact_global_minimum=False,minimum_branch=dict(state=sid,depth=depth,codes=list(prefix),suffix_count=suffix_count(depth,maxname),integer_numerator=lower),ignored_stale_descendant_code_count=5-depth,seconds=float(m.group(10)),depth_counters=counters)


def engine_prefix(path):
    data=path.read_bytes()
    marker=b'int main('
    require(marker in data,'engine main unavailable')
    prefix=data.split(marker,1)[0]
    # New wrapper introduces a strict parser before main. It is not numerical.
    prefix=prefix.split(b'I read_uint(',1)[0]
    return prefix


def compile_and_wrapper_checks(engine,tmp,compiler,input_data):
    binary=tmp/'scan'
    subprocess.run([compiler,'-std=c++17','-O3',str(engine),'-o',str(binary)],check=True,capture_output=True,text=True)
    tokens=input_data.split()
    variants={}
    variants['negative_integer']='-1 '+' '.join(tokens[1:])
    variants['truncated']=' '.join(tokens[:-1])
    variants['trailing_token']=input_data+'0\n'
    x=tokens.copy();x[4]=str(2**63-1);variants['unsafe_coefficient']=' '.join(x)
    x=tokens.copy();x[261]='2';variants['wrong_state']=' '.join(x)
    x=tokens.copy();x[4]=str(2**63);variants['integer_overflow']=' '.join(x)
    x=tokens.copy();x[3]='999';variants['wrong_threshold']=' '.join(x)
    results={}
    for name,data in variants.items():
        path=tmp/(name+'.txt');path.write_text(data)
        run=subprocess.run([str(binary),str(path)],capture_output=True,text=True,timeout=5)
        require(run.returncode!=0 and 'threshold 1/' not in run.stdout,'malformed input accepted: '+name)
        results[name]=dict(exit_code=run.returncode,reason=run.stderr.strip())
    # Compile the identical numerical prefix with only a suffix-count main.
    driver=tmp/'suffix.cpp'
    driver.write_bytes(engine_prefix(engine)+b'int main(){Engine e;for(int d=0;d<=5;++d)for(int k=0;k<4;++k)std::cout<<d<<" "<<k<<" "<<e.count(d,k)<<"\\n";}\n')
    counter=tmp/'suffix'
    subprocess.run([compiler,'-std=c++17','-O3',str(driver),'-o',str(counter)],check=True,capture_output=True,text=True)
    run=subprocess.run([str(counter)],capture_output=True,text=True,check=True)
    require(len(run.stdout.splitlines())==24,'suffix driver output')
    for line in run.stdout.splitlines():
        d,k,count=map(int,line.split())
        require(count==suffix_count(d,k),'independent suffix recurrence mismatch')
    return binary,dict(compile_exit_code=0,full_new_wrapper_run=False,malformed_input_checks=results,independent_suffix_counts_checked=24)


def exact_checks():
    witness_codes=(9,27,27,27,27)
    witness_w=tuple(F(x,9) for x in (2,2,2,2,0,1))
    witness=exact_modes(witness_codes,witness_w,3)
    require(witness==exact_supports(witness_codes,witness_w,3),'witness support reconstruction')
    expected={'block':'480681437437391/1065230103168000','sf_loss':'17331445810753829/152327904753024000','tail_loss':'43452210042754061/268813949564160000','mass':'803492421556973483/4569837142590720000','query':'16138704240676441/8017258144896000','gate':'502837644894249281/27990252498368160000','weighted':'4842375295428315876809/146234788562903040000'}
    require(all(witness[k]==F(v) for k,v in expected.items()),'exact witness changed')
    c=F(1084133,201247200)
    through31=(1-c)*witness['mass']-c*witness['weighted']
    seed180=179*witness['mass']-witness['weighted']
    require(through31==F(-983186847955838985086629,280279445151202482585600000) and seed180==F(-15998046983331451079,9748985904193536000),'negative-31 witness changed')
    rng=random.Random(20260925)
    cases=[(witness_codes,sid) for sid in range(16)]+[(tuple(rng.randrange(64) for _ in Q),rng.randrange(16)) for _ in range(32)]
    max_gap=F(0)
    for codes,sid in cases:
        w,mark=REPRESENTATIVES[sid]
        a=exact_modes(codes,w,mark)
        b=exact_supports(codes,w,mark)
        require(a==b,'127-support and 256-mode disagreement')
        bound=F(integer_bound(codes,sid),SCALE*SD)
        gap=a['gate']-bound
        require(0<=gap<=arithmetic_bounds()['gate_rounding_error_upper'],'integer/Fraction enclosure failed')
        max_gap=max(max_gap,gap)
    return dict(codes=witness_codes,weights=witness_w,mark=3,state=10,values=witness,negative31=dict(coefficient=c,envelope=through31,seed180_envelope=seed180,interpretation='Failure of this weighted envelope only; neither a covering nor an impossibility theorem.'),crosschecks=dict(seed=20260925,cases=len(cases),support_mode_equalities=len(cases)+1,integer_lower_bound_checks=len(cases),maximum_observed_rounding_gap=max_gap))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--engine',type=Path,default=Path(__file__).with_name('central_square_63_scan.cpp'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    ap.add_argument('--compiler',default='c++')
    ap.add_argument('--reuse-run',type=Path)
    ap.add_argument('--reference-engine',type=Path)
    ap.add_argument('--reference-input',type=Path)
    args=ap.parse_args()
    data=input_text()
    require(digest(data.encode())==HISTORICAL_INPUT_SHA256,'generated historical input mismatch')
    exact=exact_checks()
    rounding=arithmetic_bounds()
    with tempfile.TemporaryDirectory(prefix='central-square-63-') as tmpname:
        tmp=Path(tmpname)
        binary,checks=compile_and_wrapper_checks(args.engine,tmp,args.compiler,data)
        if args.reuse_run:
            require(args.reference_engine is not None and args.reference_input is not None,'reuse requires reference engine and input')
            require(args.reference_input.read_bytes()==data.encode(),'historical input not byte-identical')
            require(digest(args.reference_engine.read_bytes())==HISTORICAL_ENGINE_SHA256,'unexpected historical engine')
            require(digest(args.reuse_run.read_bytes())==HISTORICAL_RUN_SHA256,'unexpected historical traversal output')
            require(engine_prefix(args.engine)==engine_prefix(args.reference_engine),'numerical engine prefix changed')
            stdout=args.reuse_run.read_text()
            evidence=dict(mode='reused_completed_full_traversal',new_wrapper_full_run=False,reference_engine_sha256=digest(args.reference_engine.read_bytes()),reference_run_sha256=digest(args.reuse_run.read_bytes()),reference_input_sha256=digest(args.reference_input.read_bytes()),identical_numerical_prefix_sha256=digest(engine_prefix(args.engine)),prior_full_run_exit_code=0,prior_exit_code_source='Recorded completed execution; the seven-line output is also independently validated. New wrapper is compiled and tested but not fully traversed in reuse mode.')
        else:
            require(args.reference_engine is None and args.reference_input is None,'reference paths only apply to reuse mode')
            source=tmp/'input.txt';source.write_text(data)
            run=subprocess.run([str(binary),str(source)],capture_output=True,text=True)
            require(run.returncode==0,'full scan failed: '+run.stderr[-4000:])
            stdout=run.stdout
            checks['full_new_wrapper_run']=True
            evidence=dict(mode='new_wrapper_full_traversal',new_wrapper_full_run=True,exit_code=run.returncode,stdout_sha256=digest(stdout.encode()))
        scan=parse_run(stdout)
    rho=F(3458,405)
    haar=F(49,1000*616)/rho
    require(haar==F(3969,426025600) and haar>F(1,108000),'Haar consequence')
    result=dict(schema='central-square-63-profile-v1',scope=dict(head_primes=P,continuation_primes=(23,29),extra_original=63,original_phases='arbitrary and globally fixed',original_and_query_heights='unbounded',excluded_claims=['through31','749 enlargement','unrestricted Erdos7','Lean verification'],proof_type='ordinary reduction with complete outward-rounded integer branch certificate'),constants=dict(gain=G,scale=SCALE,factor_denominator=D,screen_denominator=SD,final_denominator=SCALE*SD,threshold=THRESHOLD),coefficients=COEF,rounded_combined_coefficients=ROUNDED,states=STATES,capped_simplex_vertices=VERTICES,branch_inputs=dict(beta_exact=BETA,beta_lower=BETA_LO,factor_lower=FAC_LO,factor_upper=FAC_HI,input_sha256=digest(data.encode()),all_factors_and_coefficients_generated=True),coverage=dict(layout_orbits=ORBITS,state_cases=CASES,burnside_formula='2^10*(4^10+3*2^10+2)/6',suffix_counts=[[suffix_count(d,k) for k in range(4)] for d in range(6)],vertex_mark_pairs_checked=180),arithmetic=rounding,exact_witness=exact,scan=scan,evidence=evidence,engine_checks=checks,consequence=dict(source_density_bound=rho,haar_lower=haar,strictly_greater_than=F(1,108000)),producer_sha256=digest(Path(__file__).read_bytes()),engine_sha256=digest(args.engine.read_bytes()))
    args.output.write_text(json.dumps(fractions_json(result),indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(dict(output=str(args.output),evidence_mode=evidence['mode'],certified_cases=scan['certified_cases'],threshold=str(THRESHOLD),haar_lower=str(haar),negative31=str(exact['negative31']['envelope'])),ensure_ascii=False))


if __name__=='__main__':
    main()
