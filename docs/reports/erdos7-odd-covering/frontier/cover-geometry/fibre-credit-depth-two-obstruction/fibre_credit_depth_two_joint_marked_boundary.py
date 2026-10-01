#!/usr/bin/env python3
"""Actual distinct-modulus examples locating missing common-root relations."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import argparse,json

def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def crt(congruences):
    a,m=0,1
    for b,n in congruences:
        a+=m*((b-a)*pow(m,-1,n)%n);m*=n
    return a,m

def calculate():
    head=[(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
          (21,0),(35,0),(63,0),(105,0),(315,0)]
    old=[x for x in range(315) if all(x%d!=a for d,a in head)]
    need(len(old)==102,'actual head support')

    def cylinder_maxima(cells,primes):
        result={}
        for d in (d for d in range(1,316) if 315%d==0):
            for mask in range(1<<len(primes)):
                hist={}
                for cell in cells:
                    key=(cell[0]%d,)+tuple(cell[j+1] for j in range(len(primes)) if mask>>j&1)
                    hist[key]=hist.get(key,0)+1
                result[d,mask]=max(hist.values())
        return result

    single=[]
    for variant in (0,1):
        originals=head+[(11,0)]
        for outside,d in enumerate((3,5,9,15,45),1):
            a,m=crt(((2%d,d),(outside,11)));originals.append((m,a))
        for d,aold,outside in ((7,2,6),(21,2,7),(35,2,8),
                               (63,47,6 if variant==0 else 8),
                               (105,47,7 if variant==0 else 9),
                               (315,47,8 if variant==0 else 10)):
            a,m=crt(((aold%d,d),(outside,11)));originals.append((m,a))
        need(len(originals)==len({m for m,a in originals})==23,'distinct odd numerical moduli')
        alive={}
        for x in old:
            alive[x]=[r for r in range(1,11)
                      if all(crt(((x,315),(r,11)))[0]%d!=a for d,a in originals)]
        cells=[(x,r) for x in old if x%45==2 for r in alive[x]]
        need(len(cells)==24,'same weighted-supported source denominator')
        maximum=cylinder_maxima(cells,(11,))
        beta=F(sum(v for (d,mask),v in maximum.items() if d%9==0),len(cells))
        single.append({'variant':variant,'originals':originals,'root_counts':[len(alive[x]) for x in old],
                       'old_points':old,'slice_cells':cells,'cell_count':len(cells),
                       'max_9_times11_query_numerator':maximum[9,1],
                       'saturated3_mean':str(beta)})
    need(single[0]['root_counts']==single[1]['root_counts'],'same r11 at EVERY actual old315 point')
    need([x['saturated3_mean'] for x in single]==['3','35/12'],'actual marked means differ')
    need([x['max_9_times11_query_numerator'] for x in single]==[6,5],'common-root query obstruction')

    multiple=[]
    marginal_update_checks=0
    for variant in (0,1):
        originals=head+[(11,0),(13,0)]
        pairs=((1,2),(2,1)) if variant==0 else ((1,1),(2,2))
        specs=((7,2,1,2),(21,2,2,1),(35,47,*pairs[0]),(63,47,*pairs[1]))
        for d,x,u,v in specs:
            a,m=crt(((x%d,d),(u,11),(v,13)));originals.append((m,a))
        need(len(originals)==len({d for d,a in originals})==17,'multioutside distinct moduli')
        cells=[]
        for x,u,v in product((2,47),(1,2),(1,2)):
            z,m=crt(((x,315),(u,11),(v,13)))
            if all(z%d!=a for d,a in originals):cells.append((x,u,v))
        need(len(cells)==4,'same pruned supported source count')
        # Reconstruct every retained marginal after each actual joint deletion.
        # Direct survivor enumeration is compared with the union-scope update.
        running=list(product((2,47),(1,2),(1,2)))
        for d,aold,u,v in specs:
            before=list(running)
            running=[cell for cell in running
                     if not (cell[0]%d==aold%d and cell[1:]==(u,v))]
            for x in (2,47):
                for mask in range(4):
                    chosen=[j for j in range(2) if mask>>j&1]
                    for values in product((1,2),repeat=len(chosen)):
                        assignment=dict(zip(chosen,values))
                        matches=lambda cell: cell[0]==x and all(
                            cell[j+1]==value for j,value in assignment.items())
                        oldmass=sum(matches(cell) for cell in before)
                        compatible=all((u,v)[j]==value for j,value in assignment.items())
                        joint=sum(cell==(x,u,v) for cell in before)
                        predicted=oldmass-int(x%d==aold%d and compatible)*joint
                        direct=sum(matches(cell) for cell in running)
                        need(predicted==direct,'same-source joint-scope deletion update')
                        marginal_update_checks+=1
        need(running==cells,'all actual joint deletions reproduce the final source')
        marginals={(x,p,r):sum(c[0]==x and c[p+1]==r for c in cells)
                   for x,p,r in product((2,47),range(2),(1,2))}
        maximum=cylinder_maxima(cells,(11,13))
        beta=F(sum(v for (d,mask),v in maximum.items() if d%9==0),4)
        multiple.append({'variant':variant,'originals':originals,'cells':cells,
                         'single_coordinate_marginals':[(list(k),v) for k,v in marginals.items()],
                         'max_9_times11_times13_query_numerator':maximum[9,3],
                         'saturated3_mean':str(beta)})
    need(multiple[0]['single_coordinate_marginals']==multiple[1]['single_coordinate_marginals'],
         'even the full conditional single-coordinate marginals are equal')
    need([r['max_9_times11_times13_query_numerator'] for r in multiple]==[2,1],
         'joint-query maxima differ')
    need([r['saturated3_mean'] for r in multiple]==['15/2','7'],'marked means differ')

    out={'scope':'Exact finite distinct-modulus CRT examples on explicitly declared supported '
         'probabilities. Neither is a cover or a counterexample to a uniform noncoverage theorem.',
         'singleton_example':'Same canonical102-point head and same r11 everywhere; common prior '
         'conditions on old45 residue2, retains all six live7 roots, then restricts by actual originals.',
         'singletons':single,
         'multioutside_example':'Common auxiliary supported prior has old315 rows2,47 and each '
         'outside coordinate11,13 in{1,2}; actual distinct mixed originals then restrict it. '
         'Not asserted to be the unpruned full-live-root source.',
         'multioutside':multiple,'exact_joint_marginal_updates':marginal_update_checks}
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=json.loads(json.dumps(calculate()))
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text())==result,
             'retained result agrees with literal CRT examples')
        print(rendered,end='')
    else:args.output.write_text(rendered)

if __name__=='__main__':main()
