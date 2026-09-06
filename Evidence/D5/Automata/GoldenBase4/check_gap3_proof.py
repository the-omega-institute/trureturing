"""Replay the finite branch certificate excluding three transient states.

Uses no SMT or SAT solver and no floating-point arithmetic. It independently
checks that every input row is exactly a Zeckendorf representation of 4^n,
recomputes its digit with integer square roots, and verifies every branch and
contradiction leaf for all eight Boolean one-zero observation maps.

This is a standalone executable checker, not a Lean kernel proof.
"""
from __future__ import annotations
from collections import deque
from math import isqrt
from pathlib import Path
import argparse,json,hashlib


def require(ok,msg):
    if not ok:raise ValueError(msg)


def load_rows(path):
    rows=[]
    for line in Path(path).read_text().splitlines():
        if not line.strip():continue
        n,d,tail,*gaps=map(int,line.split())
        require(n>=0 and tail in (0,1) and all(g>0 for g in gaps),'Invalid row domain')
        word='1'+''.join('0'*g+'1' for g in gaps)+'0'*tail
        q=v=0
        for bit in word:
            a=int(bit);q,v=v+a,q+v+2*a
        require(q==1 << (2*n),f'Incorrect power representation at n={n}')
        fp=lambda x:(x+isqrt(5*x*x))//2
        require(d==fp(4*q)-4*fp(q),f'Incorrect exact digit at n={n}')
        require((tail==0 and 1<=d<=3) or (tail==1 and 0<=d<=1),'Label palette assumption violated')
        rows.append((n,d,tail,gaps))
    require({d for _,d,t,_ in rows if t==0}=={1,2,3},'Missing three output witnesses')
    require(any(n==0 and d==2 and t==0 and not g for n,d,t,g in rows),'Missing initial-state witness')
    return rows


def problem(rows):
    nodes=[{'children':{},'obs':[]}];letters={}
    for n,d,tail,gs in rows:
        q=0
        for g in gs:
            if g not in letters:letters[g]=len(letters)
            if g not in nodes[q]['children']:
                j=len(nodes);nodes[q]['children'][g]=j;nodes.append({'children':{},'obs':[]})
            q=nodes[q]['children'][g]
        nodes[q]['obs'].append((tail,d))
    hc=3*len(letters);edges=[]
    for i,node in enumerate(nodes):
        for g,j in node['children'].items():edges.append((hc+i,hc+j,3*letters[g]))
    watch=[[] for _ in range(hc+len(nodes))]
    for i,(p,c,h) in enumerate(edges):
        for v in (p,c,h,h+1,h+2):watch[v].append(i)
    return nodes,hc,edges,watch,letters


def initial(nodes,hc,pattern):
    dom=[7]*(hc+len(nodes));dom[hc]=2
    for i,node in enumerate(nodes):
        for tail,out in node['obs']:
            mask=1<<(out-1) if tail==0 else sum(1<<t for t in range(3) if ((pattern>>t)&1)==out)
            dom[hc+i]&=mask
    return dom


def propagate(dom,edges,watch,seed=None):
    if any(x==0 for x in dom):return False
    ids=list(range(len(edges))) if seed is None else list(watch[seed])
    queue=deque(ids);queued=set(ids)
    def narrow(v,mask):
        new=dom[v]&mask
        if new==dom[v]:return bool(new)
        dom[v]=new
        for i in watch[v]:
            if i not in queued:queue.append(i);queued.add(i)
        return bool(new)
    while queue:
        i=queue.popleft();queued.remove(i)
        p,c,h=edges[i];pd=dom[p];cd=dom[c];np=nc=0
        for state in range(3):
            if pd & (1<<state):
                overlap=dom[h+state]&cd
                if overlap:np|=1<<state;nc|=overlap
        if not narrow(p,np) or not narrow(c,nc):return False
        if np.bit_count()==1:
            state=np.bit_length()-1
            if not narrow(h+state,dom[c]):return False
    return True


def replay(rows_path,proof_path):
    rows=load_rows(rows_path);nodes,hc,edges,watch,letters=problem(rows)
    lines=iter(Path(proof_path).read_text().splitlines());require(next(lines)=='gap3-proof-v1','Bad proof header')
    stats={'certificate_nodes':0,'contradiction_leaves':0,'branch_nodes':0,'output_maps_checked':0}
    def visit(dom,seed=None):
        consistent=propagate(dom,edges,watch,seed)
        row=next(lines).split();stats['certificate_nodes']+=1
        if row==['L']:
            require(not consistent,'Claimed contradiction with nonempty supported domains')
            stats['contradiction_leaves']+=1;return
        require(consistent and len(row)==3 and row[0]=='B','Invalid branching node')
        var,mask=map(int,row[1:])
        require(0<=var<hc and mask==dom[var] and mask.bit_count()>1,'Incomplete or invalid branch domain')
        stats['branch_nodes']+=1
        for state in range(3):
            if mask & (1<<state):
                child=dom.copy();child[var]=1<<state;visit(child,var)
    for pattern in range(8):
        require(next(lines)==f'P {pattern}','Missing or out-of-order output-map case')
        visit(initial(nodes,hc,pattern));stats['output_maps_checked']+=1
    require(next(lines,None) is None,'Trailing proof data')
    return {'status':'PASS','conclusion':'No typed DFAO with at most three transient states fits these power samples',
            'recurrent_state_count_restricted':False,'exact_power_rows_checked':len(rows),
            'power_indices':[r[0] for r in rows],'maximum_power_index':max(r[0] for r in rows),
            'gap_letters':len(letters),'transition_variables':hc,'trie_nodes':len(nodes),
            'uses_solver_for_replay':False,'lean_kernel_checked':False,**stats}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('rows',nargs='?',default=str(Path(__file__).with_name('gap3_core_rows.tsv')))
    ap.add_argument('proof',nargs='?',default=str(Path(__file__).with_name('gap3_refutation.txt')))
    a=ap.parse_args();report=replay(a.rows,a.proof)
    Path(__file__).with_name('gap3_replay_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
