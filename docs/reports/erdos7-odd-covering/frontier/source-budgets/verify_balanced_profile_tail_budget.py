"""Independent output-divisor convolution and geometric-tail moment verification."""
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt
from pathlib import Path
import argparse, importlib.util, json, sys
sys.dont_write_bytecode=True
def require(ok,message):
    if not ok:raise RuntimeError(message)

def up_ratio(a,b):
    require(a>=0 and b>0,'nonnegative exact upward ratio')
    q,r=divmod(a,b)
    return q+(r!=0)

def unique(pairs):
    result={}
    for key,value in pairs:
        require(key not in result,'duplicate JSON key')
        result[key]=value
    return result


def bind_certificate(base, io, source_bytes, path, producer, schema):
    raw = io.read_artifact_bytes(base/path)
    record = json.loads(raw, object_pairs_hook=io._unique)
    require(record['schema'] == schema, 'canonical certificate schema: '+path)
    producer_raw = io.read_artifact_bytes(base/producer)
    require(record['producer_sha256'] == sha256(producer_raw).hexdigest(), 'current producer: '+producer)
    source_bytes[path] = raw
    source_bytes[producer] = producer_raw
    for name, digest in record['source_sha256'].items():
        dep = io.read_artifact_bytes(base/name)
        require(sha256(dep).hexdigest() == digest, 'current dependency: '+name)
        require(name not in source_bytes or source_bytes[name] == dep, 'consistent dependency: '+name)
        source_bytes[name] = dep
    return record


def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'readable module')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def calculate(base):
    io=load_module('balanced_independent_tail_io',base/'certificate_io.py')
    source_bytes={name:io.read_artifact_bytes(base/name) for name in ('certificate_io.py', 'problem-details/57-balanced-depth-profile-and-degree-seven-frontier.md', 'frontier/source-budgets/balanced_profile_head_input.json')}
    profile_input=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_head_verification.json','frontier/source-budgets/verify_balanced_profile_head.py','balanced-profile-head-verification-v1')
    given=bind_certificate(base,io,source_bytes,'certificates/source_norms/source-budgets/balanced_profile_tail_budget.json','frontier/source-budgets/balanced_profile_tail_budget.py','balanced-profile-tail-budget-v1')
    arithmetic_input=json.loads(source_bytes['frontier/source-budgets/balanced_profile_head_input.json'],object_pairs_hook=io._unique)
    require(given['geometric_lift'] and given['B']==16384 and given['global_prime_index']==1900 and
            given['tail_stages']==1879 and given['scale']==10**18,'full finite interval and infinite lift')
    B=16384
    scale=10**18
    cap=(2*B+1)//5
    primes=[p for p in range(2,B+1) if all(p%d for d in range(2,isqrt(p)+1))]
    require(len(primes)==1900 and primes[-1]==16381,'independent trial-division prime list')
    require(arithmetic_input['prime_order']==[p for p in primes if 3<=p<=73],'all20 actual odd head primes')
    profiles=tuple(tuple(F(r) for r in row) for row in profile_input['profiles'])
    heights=tuple(arithmetic_input['heights'])
    require(given['profiles']==profile_input['profiles'],'directed profile equals proposed original input')
    require(given['epsilon_exact']==profile_input['epsilon_exact'],'same exact head optimization value')
    divisors=[[] for _ in range(cap+1)]
    for f in range(1,cap+1):
        for d in range(f,cap+1,f):
            divisors[d].append(f)

    def convolution(weights,atoms):
        length=len(atoms)
        output=[0]*(cap+1)
        for d in range(1,cap+1):
            raw=sum(weights[d//f]*atoms[f] for f in divisors[d] if f<length and atoms[f])
            output[d]=up_ratio(raw,scale)
        return output

    def multiply_upper(value,factor):
        return up_ratio(value*factor.numerator,factor.denominator)

    weights=[0]*(cap+1)
    weights[1]=scale
    mean=second=scale
    exact_head_mean=exact_head_second=F(1)
    head_atomic_checks=0
    for p,h,r in zip(arithmetic_input['prime_order'],heights,profiles):
        require(len(r)==h+1 and r[0]==1,'actual full finite height')
        require(all(F(1,p**e)<=r[e]<=r[e-1] for e in range(1,h+1)),'profile capacity assumptions')
        atoms=[F(0)]*(h+2)
        for f in range(1,h+2):
            atoms[f]=r[f-1]-(r[f] if f<=h else F(0))
        require(sum(atoms)==1 and all(a>=0 for a in atoms),'complete finite atomic law')
        first=sum((f*a for f,a in enumerate(atoms)),F(0))
        square=sum((f*f*a for f,a in enumerate(atoms)),F(0))
        require(first==1+sum(r[1:],F(0)),'finite mean identity')
        require(square==1+sum(((2*e+1)*r[e] for e in range(1,h+1)),F(0)),'finite moment identity')
        require(atoms[-1]==r[-1],'terminal high-depth mass kept')
        head_atomic_checks+=1
        # Replace the terminal K=H atom by its entire geometric continuation.
        # f=H+1+j has probability r_H*(p-1)/p^(j+1), j>=0.
        rounded=[up_ratio(a.numerator*scale,a.denominator) for a in atoms[:-1]]
        numerator=scale*r[h].numerator*(p-1)
        denominator=r[h].denominator*p
        for f in range(h+1,cap+1):
            if numerator<=denominator:
                rounded.extend([1]*(cap+1-f))
                break
            rounded.append(up_ratio(numerator,denominator))
            denominator*=p
        require(len(rounded)==cap+1,'all retained lifted atoms')
        # Sum the added geometric tail moments analytically; no high mass is lost.
        first+=r[h]/(p-1)
        square+=r[h]*(F(2*h+1,p-1)+F(2*p,(p-1)**2))
        weights=convolution(weights,rounded)
        mean=multiply_upper(mean,first)
        second=multiply_upper(second,square)
        exact_head_mean*=first
        exact_head_second*=square

    charge=0
    steps=[]
    for q in primes:
        if q<=73:continue
        cutoff=(2*q+1)//5
        upper=5*mean-(2*q+1)*scale
        upper+=sum((2*q+1-5*d)*weights[d] for d in range(1,cutoff+1))
        step=up_ratio(upper,3*(q-2))
        charge+=step
        steps.append((q,step,charge))
        # f>=2 exact atom = 5(q-1)^2/[3(q-2)q^f]. All atoms eventually
        # round to1 on this positive grid; a zero geometric atom is never assumed.
        atoms=[0]*(cap+1)
        atoms[1]=up_ratio(scale*(3*q*(q-2)-5*(q-1)),3*q*(q-2))
        numerator=scale*5*(q-1)**2
        denominator=3*(q-2)*q*q
        for f in range(2,cap+1):
            if numerator<=denominator:
                atoms[f:]=[1]*(cap+1-f)
                break
            atoms[f]=up_ratio(numerator,denominator)
            denominator*=q
        weights=convolution(weights,atoms)
        mean=multiply_upper(mean,F(3*q-1,3*(q-2)))
        second=multiply_upper(second,1+F(5*(3*q-1),3*(q-2)*(q-1)))

    C,J=F(charge,scale),F(second,scale)
    require(C==F(given['C_upper']) and J==F(given['J_upper']),'independent C/J equal supplied exact uppers')
    digest=sha256(json.dumps(steps,separators=(',',':')).encode()).hexdigest()
    require(digest==given['step_digest'] and [list(row) for row in steps]==given['stages'] and len(steps)==1879,'every independent1879-stage triple agrees')
    epsilon=F(given['epsilon_exact'])
    # Previously proved by explicit positive atanh sums: log1900>377/50 and
    # loglog1900>201/100. Thus T>1900*(131/20)^2=326059/4.
    short_threshold=F(326059,4)
    score=epsilon+C+(J-1)/(short_threshold-1)
    require(score<1,'strict pass even with independently fixed shorter threshold')
    survival=1-epsilon-C
    require(survival>0,'same-source surviving mass positive')
    gamma=1+(J-1)/survival
    require(gamma<short_threshold,'same-source Gamma below the shorter stop')
    result=dict(scope='Independent exact directed audit of this balanced fixed154 head with uniform extra digits; arbitrary finite head exponents in original tail cofactors are covered by the geometric auxiliary domination.',
                source_sha256={name:sha256(raw).hexdigest() for name,raw in source_bytes.items()},
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                finite_head_atomic_laws_checked=head_atomic_checks,
                prime_count=len(primes),tail_stages=len(steps),last_prime=primes[-1],
                retained_states=cap,maximum_queried_state=(2*primes[-1]+1)//5,
                exact_head_mean=str(exact_head_mean),exact_head_second=str(exact_head_second),
                C_upper=str(C),J_upper=str(J),stage_digest=digest,
                epsilon_exact=str(epsilon),independent_T_lower=str(short_threshold),
                independent_consumer_score_upper=str(score),survival_lower=str(survival),
                Gamma_upper=str(gamma))


    require(survival==F(given['survival_lower']) and gamma==F(given['Gamma_upper']),
            'independent same-law survivor and Gamma equal candidate values')
    require(all(io.read_artifact_bytes(base/name)==raw for name,raw in source_bytes.items()),'audit sources unchanged')
    result.update(schema='balanced-profile-tail-verification-v1',stages=[list(row) for row in steps],
                  profiles=profile_input['profiles'],
                  independent_consumer_score_decimal=float(score),
                  independent_margin=str(1-score),independent_margin_decimal=float(1-score),
                  threshold_scope='Fixed conservative T=326059/4.')
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    io=load_module('balanced_output_io',args.base/'certificate_io.py')
    result=calculate(args.base)
    path=args.base/'certificates/source_norms/source-budgets/balanced_profile_tail_verification.json'
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result==json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact canonical balanced-profile replay')
    print(json.dumps({key:result[key] for key in ('schema', 'C_upper', 'J_upper', 'tail_stages', 'independent_consumer_score_decimal')},indent=2))

if __name__=='__main__':
    main()
