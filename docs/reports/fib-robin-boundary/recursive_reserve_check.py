#!/usr/bin/env python3
"""Read-back structural and exact displayed-rounding checks; no log recomputation."""
import sys
sys.dont_write_bytecode = True

import argparse
import gzip
import hashlib
import json
from pathlib import Path


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',type=Path,required=True,help='producer output directory')
    ap.add_argument('--out',type=Path,required=True,help='JSON read-back report file')
    args=ap.parse_args()
    directory=args.input
    raw=gzip.decompress((directory/'certificate.json.gz').read_bytes())
    cert=json.loads(raw)
    result=json.loads((directory/'results.json').read_text())
    assert hashlib.sha256(raw).hexdigest()==result['certificate_sha256']
    scale=int(cert['scale'])
    num,den=cert['target']
    nodes=cert['nodes']
    roots=cert['roots']
    seen=set()
    leaves=[]
    stack=list(reversed(roots))
    while stack:
        i=stack.pop()
        assert i not in seen
        seen.add(i)
        n=nodes[i]
        assert n['index']==i
        assert n['b']-n['a']==cert['fibonacci'][n['fibonacci_length_index']]
        lo,hi=map(int,n['Gamma'])
        assert lo<=hi
        if n['status']=='leaf':
            assert lo*den>num*scale
            leaves.append(i)
        else:
            assert n['status']=='split' and lo*den<=num*scale
            il,ir=n['children']
            left,right=nodes[il],nodes[ir]
            assert left['parent']==right['parent']==i
            assert left['a']==n['a'] and left['b']==right['a'] and right['b']==n['b']
            assert left['fibonacci_length_index']==n['fibonacci_length_index']-1
            assert right['fibonacci_length_index']==n['fibonacci_length_index']-2
            assert left['depth']==right['depth']==n['depth']+1
            stack.extend([ir,il])
    assert seen==set(range(len(nodes)))
    assert leaves==cert['leaves']
    assert nodes[leaves[0]]['a']==144 and nodes[leaves[-1]]['b']==121393
    assert all(nodes[a]['b']==nodes[b]['a'] for a,b in zip(leaves,leaves[1:]))
    assert len(nodes)==2*len(leaves)-len(roots)
    expected={'B_old':156310637,'B2':191707785,'R2':191707785,
              'R3':213606663,'R4':219252586,'R':229484932}
    for name,n in expected.items():
        lo,hi=map(int,cert['diagnostic'][name])
        # Complete interval lies inside the round-to-nearest cell at 12 places.
        assert (2*n-1)*scale < 2*10**12*lo
        assert 2*10**12*hi < (2*n+1)*scale
    audit={'status':'PASS','saved_nodes_checked':len(nodes),'saved_leaves_checked':len(leaves),
           'roots_checked':len(roots),'decimal_rounding_checks':len(expected),
           'arithmetic':'integer comparisons only',
           'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'certificate_sha256':hashlib.sha256(raw).hexdigest(),
           'scope':'Saved-certificate structure and rounding; transcendental enclosures come from the producer and its audited interval engine.'}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps(audit,indent=2))


if __name__=='__main__':
    main()
