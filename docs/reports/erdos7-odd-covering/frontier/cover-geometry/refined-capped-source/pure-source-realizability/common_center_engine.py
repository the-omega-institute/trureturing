"""Exact actual clean-centre integrals and rational upper envelopes.

This module has no repository or candidate I/O. Inputs are explicit finite
colour/leaf data. Low atoms and complete means are transported separately.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import prod


def require(ok, message):
    if not ok:
        raise ValueError(message)


@dataclass(frozen=True)
class Law:
    mass: F
    mean: F
    atoms: tuple  # atoms[n], 0<=n<=low_limit; n=0 is identically zero.


def point_law(n, mass, limit):
    require(n>=1 and mass>=0, 'positive-integer point law')
    atoms=[F(0)]*(limit+1)
    if n<=limit:atoms[n]=mass
    return Law(mass,mass*n,tuple(atoms))


def q_law(q,delta,probability,centre,source,limit,cutoff=None):
    require(q>=2 and delta>0 and probability>=0 and limit>=1,'coordinate-law input')
    if cutoff is not None:require(cutoff>=1,'positive finite query cutoff')
    if probability==0:return point_law(1,F(0),limit)
    if centre!=source:return point_law(1,probability,limit)
    require(probability>=delta/q,'one entire clean root in this live colour')
    a=[F(0)]*(limit+1)
    a[1]=probability-delta/q
    if cutoff is None:
        for n in range(2,limit+1):a[n]=delta*F(q-1,q**n)
        mean=probability+delta/F(q-1)
    else:
        for n in range(2,min(cutoff,limit)+1):a[n]=delta*F(q-1,q**n)
        if cutoff+1<=limit:a[cutoff+1]=delta/F(q**cutoff)
        mean=probability+delta*sum((F(1,q**e) for e in range(1,cutoff+1)),F(0))
    return Law(probability,mean,tuple(a))


def ternary_law(source_leaf,centre_leaf,limit,cutoff=None):
    require(limit>=1,'positive atom limit')
    if cutoff is not None:require(cutoff>=2,'ternary leaf-resolving cutoff')
    if source_leaf%3!=centre_leaf%3:return point_law(1,F(1),limit)
    if source_leaf!=centre_leaf:return point_law(2,F(1),limit)
    a=[F(0)]*(limit+1)
    if cutoff is None:
        for n in range(3,limit+1):a[n]=F(2,3**(n-2))
        mean=F(7,2)
    else:
        for n in range(3,min(cutoff,limit)+1):a[n]=F(2,3**(n-2))
        if cutoff+1<=limit:a[cutoff+1]=F(1,3**(cutoff-2))
        mean=F(3)+sum((F(1,3**j) for j in range(1,cutoff-1)),F(0))
    return Law(F(1),mean,tuple(a))


def hinge(law,h):
    h=F(h)
    require(h>=0 and h<=len(law.atoms),'threshold within retained low-atom interface')
    return law.mean-h*law.mass+sum(((h-n)*law.atoms[n]
               for n in range(1,len(law.atoms)) if n<h),F(0))


def centres(primes,deltas,probabilities,leaves,table,low_limit=27,
            nonternary_cutoffs=None,ternary_cutoff=None):
    """All clean-centre actual laws via modewise multiplicative convolution.

    table[(leaf_index,source_colour_0,...)] is u, with pi not yet multiplied.
    The output index replaces each source index by its centre index.
    No maxima over source cells or layouts are taken in this function.
    """
    require(len(primes)==len(deltas)==len(probabilities),'source coordinate dimensions')
    require(len(set(primes))==len(primes) and len(set(leaves))==len(leaves),'distinct coordinates/leaves')
    require(all(leaf%3!=0 for leaf in leaves),'declared live ternary roots')
    for block in probabilities:require(sum(block)==1 and all(p>=0 for p in block),'source probability law')
    sizes=(len(leaves),)+tuple(len(block) for block in probabilities)
    indices=tuple(product(*(range(size) for size in sizes)))
    require(set(table).issubset(indices),'retained table index domain')
    require(all(v>=0 for v in table.values()),'nonnegative retained table')
    require(low_limit>=1,'low-atom domain')
    divs={n:tuple(d for d in range(1,n+1) if n%d==0) for n in range(1,low_limit+1)}
    stats={'categorical_positions':len(indices),'low_atom_slots':len(indices)*low_limit,
           'atom_terms_considered':0,'nonzero_atom_products':0,'scalar_product_terms':0,
           'coordinate_transforms':0,'largest_denominator_bits':0}
    tensor={idx:point_law(1,table.get(idx,F(0)),low_limit) for idx in indices}

    def transform(axis,kernels):
        nonlocal tensor
        out={}
        for idx in indices:
            m=e=F(0)
            atoms=[F(0)]*(low_limit+1)
            target=idx[axis]
            for source in range(sizes[axis]):
                prev=tensor[idx[:axis]+(source,)+idx[axis+1:]]
                kernel=kernels[target,source]
                m+=prev.mass*kernel.mass
                e+=prev.mean*kernel.mean
                stats['scalar_product_terms']+=2
                for n in range(1,low_limit+1):
                    for d in divs[n]:
                        stats['atom_terms_considered']+=1
                        a,b=prev.atoms[d],kernel.atoms[n//d]
                        if a and b:
                            atoms[n]+=a*b
                            stats['nonzero_atom_products']+=1
            require(m>=0 and e>=m and all(v>=0 for v in atoms),'positive transported actual law')
            require(sum(atoms)<=m and sum(n*atoms[n] for n in range(1,low_limit+1))<=e,'complete mean/mass dominate low atoms')
            out[idx]=Law(m,e,tuple(atoms))
        tensor=out
        stats['coordinate_transforms']+=1

    for i,q in enumerate(primes):
        cutoff=None if nonternary_cutoffs is None else nonternary_cutoffs[i]
        matrix={(c,s):q_law(q,deltas[i],probabilities[i][s],c,s,low_limit,cutoff)
                for c in range(sizes[i+1]) for s in range(sizes[i+1])}
        transform(i+1,matrix)
    matrix={(c,s):ternary_law(leaves[s],leaves[c],low_limit,ternary_cutoff)
            for c in range(sizes[0]) for s in range(sizes[0])}
    transform(0,matrix)
    stats['largest_denominator_bits']=max(v.denominator.bit_length()
           for law in tensor.values() for v in (law.mass,law.mean,*law.atoms))
    return tensor,stats


def interval_envelope(lines,left,right):
    """Exact upper envelope of labelled affine lines alpha+beta*x.

    Returns nonempty segments covering [left,right]. Equal slope/intercept
    ties use repr(label), without claiming uniqueness of any optimum.
    """
    left,right=F(left),F(right)
    require(left<right and lines,'nonempty bounded envelope problem')
    by_slope={}
    for label,alpha,beta in lines:
        alpha,beta=F(alpha),F(beta)
        current=by_slope.get(beta)
        row=(label,alpha,beta)
        if current is None or alpha>current[1] or (alpha==current[1] and repr(label)<repr(current[0])):
            by_slope[beta]=row
    hull=[]
    for beta in sorted(by_slope):
        line=by_slope[beta]
        start=None
        while hull:
            old,oldstart=hull[-1]
            crossing=(old[1]-line[1])/(line[2]-old[2])
            if oldstart is not None and crossing<=oldstart:
                hull.pop()
            else:
                start=crossing
                break
        if not hull:start=None
        hull.append((line,start))
    segments=[]
    for i,(line,start) in enumerate(hull):
        end=hull[i+1][1] if i+1<len(hull) else None
        a=left if start is None else max(left,start)
        b=right if end is None else min(right,end)
        if a<b:
            segments.append({'left':a,'right':b,'label':line[0],'alpha':line[1],'beta':line[2]})
    require(segments and segments[0]['left']==left and segments[-1]['right']==right,'envelope covers interval')
    for a,b in zip(segments,segments[1:]):require(a['right']==b['left'],'envelope no gap')
    return segments


def centre_envelope(curves,max_threshold):
    """Curves map centre labels to exact integer hinges at 0..max_threshold."""
    require(max_threshold>=1 and curves,'finite centre curves')
    require(all(len(v)==max_threshold+1 for v in curves.values()),'complete threshold grid')
    out=[]
    for j in range(max_threshold):
        lines=[]
        for label,v in curves.items():
            beta=v[j+1]-v[j]
            lines.append((label,v[j]-j*beta,beta))
        out.extend(interval_envelope(lines,F(j),F(j+1)))
    return out


def affine_budget_max(envelope,intercept,slope):
    """Maximum of an affine budget minus a supplied exact upper envelope.

    For the centre-envelope gate this is a concave piecewise affine function
    on each unit interval. Every rational envelope breakpoint is retained.
    """
    require(envelope,'nonempty envelope')
    values={}
    for segment in envelope:
        for h in (segment['left'],segment['right']):
            y=segment['alpha']+segment['beta']*h
            v=F(intercept)+F(slope)*h-y
            if h in values:require(values[h]==v,'continuous envelope at crossing')
            values[h]=v
    best=max(values,key=lambda h:(values[h],-h))
    return {'threshold':best,'value':values[best],'breakpoint_values':values}
