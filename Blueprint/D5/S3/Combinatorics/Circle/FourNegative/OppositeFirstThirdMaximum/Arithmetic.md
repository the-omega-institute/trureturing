# Dyadic quotients and six simultaneous margins

## Abstract

Dyadic quotients and six simultaneous margins

Assume 2<=b, 2<=d, b<a and d<a. Put x=2^a, y=2^b, t=2^d, eta=2^(a-b), C=1+y*(x+1), A=x*C+1, B=1+t*(x+1)+x*y*t, L=(x+1)*(1+x*t), and K=C+x*y*t. The enlarged shared heads are SU=2*B-1, SV=2*L-(x+1), and SW=2*K-C. The six gates are the doubled mixed margins needed by the two physical orders.

For b<d the quotient m=floor((2*A-B-1)/(2*K)) lies between zero and 2^(a-d)-1. Writing R for the remainder reduces the remaining enlarged lower margin to (x-2*m)*C-2*R-2. The dyadic ratio g=2^(a-d) is 2, 4, or at least 8. At g=2 and g=4 the quotient is exactly 1 and 3; explicit polynomial identities give the margin. At g>=8 the remainder bound and the quotient cap suffice. The adjacent case d=b+1 is included.

For d+2<=b put h=floor((2*A+B-1)/(2*K)) and m=h-1. The enlarged lower margin is (x-2*h)*C-2*R. When t>=8, h<=g suffices; when t=4, a polynomial positive for y>=16 and g>=8 proves h<=g-2. These are unbounded inequalities, with no finite enumeration of exponent tuples.

choose_mask converts the nonnegative integer selector to a natural mask only after proving its capacity bound m<2^(a-1). It supplies all six margins for the original physical construction. The other quotient and polynomial lemmas establish these same margins within its proof.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
