# Two independent unbounded gaps

## Abstract

A common physical order for all equal-outer-three gaps

**Theorem 1.1 (The complete family).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint.actualSource_equal_outer_three_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint.actualSource_equal_outer_three_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every independent pair of natural numbers s,b with s>=2 and b>=2, let k=3s+b and A=1+2^s+2^(s+b)+2^(2s+b). One permutation sigma of every original Fin(k) occurrence and one literal cut j<=k satisfy both OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)). Each predicate includes total zero and every natural take-prefix, including empty, full and overlong takes. No primitivity, distinct-value, feasibility, or finite-bound assumption is imposed.

This is the caller's ordinary construction. Put q=2^s, y=2^b and N=q^3*y-1. The old heads are A=(q+1)(qy+1), B=q^2*y+q^2+q+1, L=(q+1)(q^2+1), M=(q^2+q+1)y+1; enlarged heads are 2A, Bn=2B-1, Ln=2L-q-1, Mn=2M-1-y-qy. The native U,V,W,X chains have lengths s,s,b,s and offsets 0,s,2s,2s+b. Their positive entries are literal dyadic multiples of their heads, and their terminal values are -(N-H)/2 for the corresponding successor head H. The enlarged modulus is 2N+1; its terminal values are -((2N+1)-Hn)/2 with native successor heads Bn,Ln,Mn,A. The fresh label k has value A. The exact old recurrences qA=N+B, qB=N+L, yL=N+M, qM=N+A and enlarged counterparts are used to normalize every terminal.

In the upper range b>=s+2, transfer a literal subset T of W positives into the V bank. When s>=3, put h=b-s-2 and choose local indices [0,h) together with h+1, with weight 3*2^h-1. At (s,b)=(2,4), choose local index 1, with weight 2. When s=2,b>=5, put h=b-5 and choose [0,h) together with h+2, with weight 5*2^h-1. Each chosen index lies strictly below the W terminal, and the complementary list preserves every remaining occurrence. The negative terminal order is W,U,X,V; each terminal follows its positive bank, and the fresh label is inserted immediately after the U terminal. The inventory is a permutation of the full physical label range.

Write r=2^(s-1), z=2^(b-1), and v=1+weight(T). The upper old bank masses in terminal order are (z-v)L, (r-1)A, (r-1)M, (r-1)B+(v-1)L. Their negative increments are M-zL, B-rA, A-rM, L-rB. The enlarged row replaces heads by 2A,Bn,Ln,Mn, uses the corresponding successor heads, and adds fresh A to the X bank. The upper arithmetic proves exactly the nonnegative post-terminal seams, the four peak upper bounds, and terminal zero in both rows. For s>=3 substitute r=4+Q, 2^h=1+H; for s=2,b>=5 substitute 2^h=1+H; Q,H are nonnegative. The corner is checked exactly. These integral polynomial charts are unbounded estimates.

In the lower range s>=b+2, let h=s-b-1 and m=2^h, so q=2ym, y>=4 and m>=2. Move V local indices [0,h) into the W-positive bank. Their weight is p=m-1, and h<=s-3 keeps them strictly below the V terminal. The negative terminal order is X,U,V,W. The X and U banks are native, the V bank is the remaining V positives, and the W bank consists of native W positives followed by the transferred V labels. Insert the fresh label first, at literal cut zero. Disjoint consecutive ranges and their terminal labels prove the exact physical inventory.

The lower old post-terminal seams are A-M, B-M, L-M-pB, zero; the enlarged seams after the initial fresh entry are 2A-Mn, Bn-Mn, Ln-Mn-pBn, zero. The successor heads in this order are A,B,L,M and A,Bn,Ln,Mn. With r=2^(b-1), the old bank masses are (2rm-1)M, (2rm-1)A, (2rm-1-p)B, (r-1)L+pB, and enlarged masses use Mn,2A,Bn,Ln with fresh A in the first bank. Substitute r=2+R and m=2+H, R,H>=0. Every seam and peak margin has a nonnegative integral coefficient expansion. The old strip bound is N/2=64*r^4*m^3-1 and the enlarged bound is N=128*r^4*m^3-1. Positivity within each bank extends the endpoint estimates to every prefix; source_zero supplies both exact zero totals.

The remaining range has b<=s+1 and s<=b+1. The existing BalancedGaps.actualSource_balanced_gaps_joint_lift applies directly at (s,b,s,s), including every equality boundary; no new balanced wrapper is introduced. These three ranges exhaust every s,b>=2. The bridge lift_order retains the original Fin labels and all prefixes, and marked_word identifies the enlarged list with the same sigma and its literal ear cut. The construction and full ordinary proof are attributed to the caller; earlier Pro support covered only partial polynomial and index validation. The unrestricted independent four-gap assertion J and C3.1 remain OPEN.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Endpoint.actualSource_equal_outer_three_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint](../BalancedGaps/Endpoint.md)
