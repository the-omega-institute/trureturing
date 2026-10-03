"""Exact one-shallow-axis/all-other-depth slot comparison.

Finite controls of an ordinary conditional proof, not Lean verification.
Read only the supplied FC36 inventory and write only the supplied result.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    raw = Path(args.input).read_bytes()
    data = json.loads(raw)
    checks = 0
    def need(ok, message):
        nonlocal checks
        checks += 1
        if not ok:
            raise ValueError(message)
    primes = data['primes']
    heights = dict(zip(primes,data['heights']))
    c = {p:F((p-1)*p**h,(p-2)*p**h+1) for p,h in heights.items()}
    star_roots = {(p,e):t for p,e,t in data['star_roots']}
    need(all(star_roots[p,e] == (1 if p==5 else 2)
             for p in primes for e in range(1,heights[p]+1)), 'Complete original star metadata')
    B = {(p,t):c[p]*sum((F(1,p**e) for e in range(1,heights[p]+1)
                         if star_roots[p,e]==t),F(0)) for p in primes for t in (1,2)}
    selected=dict(data['selected_witness'])
    need(len(selected)==len(data['selected_witness'])==2138,'Distinct original inventory')
    exponents={}
    coefficients={}
    for d,t in selected.items():
        n=d
        exp={}
        u=F(1)
        for p in primes:
            e=0
            while n%p==0:
                n//=p
                e+=1
            if e:
                exp[p]=e
                u*=c[p]/p**e
        need(n==1,'Source profile contains every factor')
        exponents[d]=exp
        g=F(1)
        for p in primes:
            if p not in exp:
                g*=1-B[p,t]
        coefficients[d]=u*g
    records=[]
    positive=[]
    for t in (1,2):
        for p in primes:
            S=p*(1-B[p,t])/c[p]
            k=S.numerator//S.denominator
            rho=S-k
            for q in primes:
                if p==q:
                    continue
                J=q-1-int(star_roots.get((q,1))==t)
                labels=sorted(d for d,r in selected.items()
                              if r==t and exponents[d].get(p)==1 and exponents[d].get(q,0)>=1)
                weights=sorted(((coefficients[d],d) for d in labels),reverse=True)
                K=k*J+min(k,J)
                L=J+int(k<J) if rho else 0
                total_slots=p*J+min(p,J)
                need(len(weights)<=total_slots,'Whole-minimal finite cell-capacity relaxation')
                exact_slots=[F(1)]*K+[rho]*L+[F(0)]*(total_slots-K-L)
                need(len(exact_slots)==total_slots and all(0<=v<=1 for v in exact_slots), 'Concentrated slot count')
                independent=sum((a for a,d in weights),F(0))
                upper=sum((a*v for (a,d),v in zip(weights,exact_slots)),F(0))
                delta=(1-rho)*sum((a for a,d in weights[K:K+L]),F(0))+sum((a for a,d in weights[K+L:]),F(0))
                need(independent-upper==delta and delta>=0,'Exact independent-charge deficit')
                record={
                    'root':t,'shallow_prime':p,'arbitrary_depth_prime':q,
                    'column_count':J,'source_row_sum':str(S),'full_rows':k,
                    'fractional_row_mass':str(rho),'full_slots':K,'fractional_slots':L,
                    'label_count':len(labels),'labels':labels,
                    'independent_charge':str(independent),'relaxed_upper':str(upper),
                    'delta':str(delta),'delta_decimal':float(delta),
                    'ranked_loss_coefficients':[[d,str(a)] for a,d in weights[K:]],
                    'loss_ranks_are_not_actual_label_losses':True
                }
                records.append(record)
                if delta:
                    positive.append(record)
    need(len(records)==220,'All ordered prime-pair/root buckets')
    need([(r['root'],r['shallow_prime'],r['arbitrary_depth_prime']) for r in positive]
         ==[(1,5,11),(1,5,13),(1,5,17),(1,5,19)],'Exactly four positive source-uniform slot bounds')
    r11=positive[0]
    need(r11['label_count']==27 and r11['full_slots']==22 and r11['fractional_slots']==11,'27-label mixed-depth bucket')
    need(F(r11['delta'])==F(5871989479650501664074332,30908074423698266486925085881),'Exact root-1 5/11 credit')
    shallow11=[d for d in r11['labels'] if exponents[d][11]==1]
    deep11=[d for d in r11['labels'] if exponents[d][11]>=2]
    need(len(shallow11)==19 and deep11==[605,6655,7865,10285,11495,13915,17545,18755],'Eight deeper labels share the same table')

    # Independent finite control: every possible set of doubled rows is
    # realizable by an injection into columns. Enumerate all such sets,
    # rather than using the theorem's choice of largest rows.
    control_cases=[(2,1,F(1,2)),(3,2,F(5,2)),(4,2,F(7,2)),
                   (5,3,F(2)),(5,10,F(1563,625)),(5,12,F(1563,625)),
                   (5,16,F(1563,625)),(5,18,F(1563,625))]
    enumerated_slot_lists=0
    weighted_controls=0
    for p,J,S in control_cases:
        k=S.numerator//S.denominator
        rho=S-k
        vertices=[]
        for full in combinations(range(p),k):
            partials=[i for i in range(p) if i not in full] if rho else [None]
            for partial in partials:
                vertices.append([F(1) if i in full else rho if i==partial else F(0) for i in range(p)])
        extra_sets=[set(I) for size in range(min(p,J)+1) for I in combinations(range(p),size)]
        N=p*J+min(p,J)
        K=k*J+min(k,J)
        L=J+int(k<J) if rho else 0
        target=[F(1)]*K+[rho]*L+[F(0)]*(N-K-L)
        W=[F(N-i, N+1)+F(1,(i+2)**2) for i in range(N)]
        expected=sum((a*v for a,v in zip(W,target)),F(0))
        for R in vertices:
            best=F(-1)
            for extras in extra_sets:
                slots=sorted([R[i] for i in range(p) for _ in range(J)]+[R[i] for i in extras],reverse=True)
                slots += [F(0)]*(N-len(slots))
                need(all(a<=b for a,b in zip(slots,target)),'Every row matching is majorized by stated slots')
                best=max(best,sum((a*v for a,v in zip(W,slots)),F(0)))
                enumerated_slot_lists+=1
            need(best==expected,'Concentrated bound is attained in the complete-grid relaxation')
            weighted_controls+=1
        # A nonvertex source on the SAME capped simplex exercises the
        # convex upper bound while all assignment coefficients stay fixed.
        R=[(2*a+3*b)/5 for a,b in zip(vertices[0],vertices[-1])]
        best=max(sum((a*v for a,v in zip(W,sorted([R[i] for i in range(p) for _ in range(J)]
                  +[R[i] for i in extras],reverse=True))),F(0)) for extras in extra_sets)
        need(sum(R,F(0))==S and best<=expected,'Nonvertex source bound with fixed coefficients')
        weighted_controls+=1
    result={
        'contract':'H3=1 globally class-count-then-modulus-sum minimal hypothetical cover; same source, original labels/phases, and fixed FC34 enlarged B. Exactly one prime exponent is required to be one; the second prime has arbitrary positive exponent. No unrestricted covering theorem or Lean check.',
        'input':args.input,'input_sha256':sha256(raw).hexdigest(),
        'checks':checks,'bucket_count':len(records),'positive_bucket_count':len(positive),
        'control_cases':len(control_cases),'enumerated_slot_lists':enumerated_slot_lists,
        'weighted_controls':weighted_controls,'positive_buckets':positive,
        'shallow_5_11':shallow11,'deep_5_11':deep11,'buckets':records,
        'combination_boundary':'The ranked loss terms do not identify which actual labels lose mass. Overlapping bucket credits cannot be added without a labelwise or fractional-cover justification.'
    }
    Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'checks':checks,'enumerated_slot_lists':enumerated_slot_lists,'weighted_controls':weighted_controls,
        'positive':[{k:r[k] for k in ('root','shallow_prime','arbitrary_depth_prime','label_count','full_slots','delta','delta_decimal')}
                    for r in positive]},sort_keys=True))


if __name__=='__main__':
    main()
