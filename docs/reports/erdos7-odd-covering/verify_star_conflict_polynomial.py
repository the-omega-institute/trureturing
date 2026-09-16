#!/usr/bin/env python3
"""Exact conflict-polynomial obstruction for the validated star family."""
from fractions import Fraction as F
from math import prod, gcd

P=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73)

def polynomial_value(primes,heights,z):
    a={p:sum(F(1,p**e) for e in range(1,heights[p]+1)) for p in primes}
    base=prod(1-z*a[p] for p in primes[1:])
    return (1-z*a[3])*base+sum(
        prod(1-z*a[p]*(1+F(1,3**i)) for p in primes[1:])-base
        for i in range(1,heights[3]+1))

def check_direct_small_graph():
    primes=(3,5,7)
    heights={p:2 for p in primes}
    events=[]
    for p in primes:
        for e in range(1,3):
            events.append((p**e,p**(e-1)-1))
    for p in primes[1:]:
        for i in range(1,3):
            for j in range(1,3):
                d1,d2=3**i,p**j
                r1,r2=2*3**(i-1)-1,2*p**(j-1)-1
                d=d1*d2
                events.append((d,(r1*d2*pow(d2,-1,d1)+r2*d1*pow(d1,-1,d2))%d))
    adjacency=[sum(1<<j for j,(e,s) in enumerate(events)
                   if (r-s)%gcd(d,e)) for d,r in events]
    for z in (F(1),F(1,2),F(2)):
        direct=F(0)
        for mask in range(1<<len(events)):
            selected=[i for i in range(len(events)) if mask>>i&1]
            if all(not(adjacency[i]&mask) for i in selected):
                direct+=prod(-z/F(events[i][0]) for i in selected)
        if direct!=polynomial_value(primes,heights,z):
            raise ValueError('closed polynomial versus direct CRT conflict graph')

if __name__=='__main__':
    check_direct_small_graph()
    heights={p:31 if p==3 else 8 for p in P}
    value=polynomial_value(P,heights,F(1))
    if not -F(7,1000)<value<-F(69,10000):
        raise ValueError('signed polynomial interval')
    print('PASS: star Z(1) is strictly between -7/1000 and -69/10000; decimal',float(value))
    print('The reduced actual star family is outside strict conflict-graph Shearer; its survivor set is nevertheless nonempty.')
