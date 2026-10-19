# The full coupled observation-compatible coordinate theorem

## Abstract

One coordinate realization of the original observation lift couples the symplectic split, the positive energy blocks, the canonical permutation, and both Williamson normal forms.

**Theorem 1.1 (Original data and one shared coordinate realization).**

$$\forall (n : \mathbb{N}), \forall (r : \mathbb{N}), \forall (S : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \mathbb{R}\right)), \forall (O : \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \mathbb{R}\right)), \forall (K : \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right)), ((\operatorname{PosDef}\left(S\right)) \land (\operatorname{Surjective}\left(\operatorname{mulVec}\left(O\right)\right)) \land (O \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot S = K \cdot O) \land (0 < r) \land (r < 2 \cdot n)) \Rightarrow \operatorname{Nonempty}\left(\operatorname{CoupledCoordinates}\left(S, O\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OriginalDataCoupledCoordinates.original_data_coupled_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural number m, I_m is Fin m plus Fin m and C_m is the real functions on I_m. The block index I_k plus I_h represents C_k times C_h by Sum.elim. Write Jplus_m=[[0,I],[-I,0]]=-Matrix.J (Fin m) real. The first half of each Darboux basis is labelled q and the second p because its inl/inr pairing is positive delta. Matrix(e) always means the standard-coordinate matrix of the displayed linear equivalence e.

The only hypotheses are the original positive definite S, surjective O, closure O(Jplus_n S)=KO, and the original strict bounds 0<r<2n. Define P=OS-inverse O-transpose, L=S-inverse O-transpose P-inverse, U=range L, and V=ker O. No invertibility, complementarity, nondegeneracy, evenness, invariant lift, or coordinate basis is assumed.

The result is one inhabitant of CoupledCoordinates S O. All eight groups below refer to the same fields of that inhabitant. Choose one such inhabitant and keep it fixed throughout all the displays. The typed witnesses and all clauses below are read together for this one inhabitant, not as separate existential choices. P,L,Sv,Sh,Jb,Dv,Dh,W,Pi,e and iota are definitionally fixed abbreviations, not additional premises or independently chosen replacements.

### Typed witnesses and fixed definitions

$$
k : \mathbb{N}
$$

$$
h : \mathbb{N}
$$

$$
Tv : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \mathbb{R}\right)
$$

$$
Th : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \mathbb{R}\right)
$$

$$
B : \operatorname{LinearEquiv}\left(\mathbb{R}, (\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right) \to \mathbb{R}), (\operatorname{Fin}\left(r\right) \to \mathbb{R})\right)
$$

$$
T : \operatorname{LinearEquiv}\left(\mathbb{R}, (\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right) \to \mathbb{R}), (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{R})\right)
$$

$$
Wv : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \mathbb{R}\right)
$$

$$
Wh : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \mathbb{R}\right)
$$

$$
nuv : (\operatorname{Fin}\left(k\right) \to \mathbb{R})
$$

$$
nuh : (\operatorname{Fin}\left(h\right) \to \mathbb{R})
$$

$$
Bhat : \operatorname{LinearEquiv}\left(\mathbb{R}, (\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right) \to \mathbb{R}), (\operatorname{Fin}\left(r\right) \to \mathbb{R})\right)
$$

$$
That : \operatorname{LinearEquiv}\left(\mathbb{R}, (\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right) \to \mathbb{R}), (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{R})\right)
$$

$$
R : \operatorname{LinearEquiv}\left(\mathbb{R}, (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{R}), (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{R})\right)
$$

$$
P : \operatorname{Matrix}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right)
$$

$$
L : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Fin}\left(r\right), \mathbb{R}\right)
$$

$$
Sv : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \mathbb{R}\right)
$$

$$
Sh : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \mathbb{R}\right)
$$

$$
Jb : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right), \operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right), \mathbb{R}\right)
$$

$$
Dv : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \mathbb{R}\right)
$$

$$
Dh : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right), \mathbb{R}\right)
$$

$$
W : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right), \operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right), \mathbb{R}\right)
$$

$$
e : \operatorname{Equiv}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(h\right)\right), \operatorname{Fin}\left(n\right)\right)
$$

$$
iota : \operatorname{Equiv}\left(\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)\right)
$$

$$
Pi : \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \mathbb{R}\right)
$$

$$
PiEquiv : \operatorname{LinearEquiv}\left(\mathbb{R}, (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{R}), (\operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right) \to \mathbb{R})\right)
$$

$$
r = 2 \cdot k
$$

$$
n = k + h
$$

$$
0 < k
$$

$$
0 < h
$$

$$
P = O \cdot \operatorname{inv}\left(S\right) \cdot \operatorname{transpose}\left(O\right)
$$

$$
L = \operatorname{inv}\left(S\right) \cdot \operatorname{transpose}\left(O\right) \cdot \operatorname{inv}\left(P\right)
$$

$$
Sv = \operatorname{transpose}\left(Tv\right) \cdot S \cdot Tv
$$

$$
Sh = \operatorname{transpose}\left(Th\right) \cdot S \cdot Th
$$

$$
Jb = \operatorname{fromBlocks}\left(-\operatorname{MatrixJ}\left(\operatorname{Fin}\left(k\right), \mathbb{R}\right), 0, 0, -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(h\right), \mathbb{R}\right)\right)
$$

$$
Dv = \operatorname{fromBlocks}\left(\operatorname{diagonal}\left(nuv\right), 0, 0, \operatorname{diagonal}\left(nuv\right)\right)
$$

$$
Dh = \operatorname{fromBlocks}\left(\operatorname{diagonal}\left(nuh\right), 0, 0, \operatorname{diagonal}\left(nuh\right)\right)
$$

$$
W = \operatorname{fromBlocks}\left(Wv, 0, 0, Wh\right)
$$

### C1–C3: original images and actual coordinate equivalences

$$
\operatorname{Injective}\left(\operatorname{mulVec}\left(Tv\right)\right)
$$

$$
\operatorname{Injective}\left(\operatorname{mulVec}\left(Th\right)\right)
$$

$$
\operatorname{range}\left(\operatorname{mulVecLin}\left(Tv\right)\right) = \operatorname{range}\left(\operatorname{mulVecLin}\left(L\right)\right)
$$

$$
\operatorname{range}\left(\operatorname{mulVecLin}\left(Th\right)\right) = \operatorname{ker}\left(\operatorname{mulVecLin}\left(O\right)\right)
$$

$$
O \cdot Tv = \operatorname{matrix}\left(B\right)
$$

$$
O \cdot Th = 0
$$

$$
Tv = L \cdot \operatorname{matrix}\left(B\right)
$$

$$
\forall (xv : (\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right) \to \mathbb{R})), \forall (xh : (\operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right) \to \mathbb{R})), \operatorname{T}\left(\operatorname{SumElim}\left(xv, xh\right)\right) = \operatorname{mulVec}\left(Tv, xv\right) + \operatorname{mulVec}\left(Th, xh\right)
$$

$$
\operatorname{matrix}\left(T\right) = \operatorname{columns}\left(Tv, Th\right)
$$

$$
O \cdot \operatorname{matrix}\left(T\right) = \operatorname{columns}\left(\operatorname{matrix}\left(B\right), 0\right)
$$

Apply original_data_symplectic_retract to the original S,O,K. Its restricted-radical argument tests x in ker O against (Jplus_n S)x; the vanishing pairing is negative strictly positive energy unless x=0. That argument remains on the live dependency path to the two returned Darboux bases. Include their vectors in the ambient space to obtain the columns of Tv and Th. The supplier Basis.equivFun gives their coordinate equivalences onto exactly U and V. Compose the visible equivalence with the bridge's actual observation restriction to get B. The supplier Submodule.prodEquivOfIsCompl assembles T from these same two basis maps. The returned dimension equalities and the strict bounds imply k,h>0.

### C4–C5: symplectic and energy congruences for the same T

$$
\operatorname{transpose}\left(Tv\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot Tv = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(k\right), \mathbb{R}\right)
$$

$$
\operatorname{transpose}\left(Th\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot Th = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(h\right), \mathbb{R}\right)
$$

$$
\operatorname{transpose}\left(Tv\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot Th = 0
$$

$$
\operatorname{transpose}\left(Th\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot Tv = 0
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(T\right)\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot \operatorname{matrix}\left(T\right) = Jb
$$

$$
\operatorname{PosDef}\left(Sv\right)
$$

$$
\operatorname{PosDef}\left(Sh\right)
$$

$$
\operatorname{transpose}\left(Tv\right) \cdot S \cdot Th = 0
$$

$$
\operatorname{transpose}\left(Th\right) \cdot S \cdot Tv = 0
$$

$$
Sv = \operatorname{transpose}\left(\operatorname{matrix}\left(B\right)\right) \cdot \operatorname{inv}\left(P\right) \cdot \operatorname{matrix}\left(B\right)
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(T\right)\right) \cdot S \cdot \operatorname{matrix}\left(T\right) = \operatorname{fromBlocks}\left(Sv, 0, 0, Sh\right)
$$

Read the Darboux pairings as matrix entries. Alternation gives the reverse inr/inl pairing with a minus sign, producing Jplus in both diagonal blocks. The bridge identifies the exact symplectic orthogonal U-perp with V, giving the upper-right zero block; transposition and skew symmetry give the lower-left zero block. Its energy orthogonality gives the upper-right energy zero block; symmetry of S gives the lower-left block. Positive congruence with the injective Tv and Th proves positivity of exactly Sv=Tv-transpose S Tv and Sh=Th-transpose S Th. The original lift satisfies L-transpose S=P-inverse O and OL=I, hence L-transpose S L=P-inverse. Substitution of Tv=LB proves Sv=B-transpose P-inverse B.

### C6–C7: canonical ordering and every covector

$$
e = \operatorname{modeConcat}\left(n, k, h\right)
$$

$$
iota = \operatorname{blockToGlobal}\left(n, k, h\right)
$$

$$
PiEquiv = \operatorname{canonicalPiEquiv}\left(n, k, h\right)
$$

$$
\forall (i : \operatorname{Sum}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right)\right)), \forall (j : \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right)), \operatorname{entry}\left(Pi, i, j\right) = \operatorname{if}\left(\operatorname{iota}\left(i\right) = j, 1, 0\right)
$$

$$
\forall (z : (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right) \to \mathbb{R})), \operatorname{mulVec}\left(Pi, z\right) = \operatorname{SumElim}\left(\operatorname{SumElim}\left(\lambda (i : \operatorname{Fin}\left(k\right)). \operatorname{z}\left(\operatorname{inl}\left(\operatorname{e}\left(\operatorname{inl}\left(i\right)\right)\right)\right), \lambda (i : \operatorname{Fin}\left(k\right)). \operatorname{z}\left(\operatorname{inr}\left(\operatorname{e}\left(\operatorname{inl}\left(i\right)\right)\right)\right)\right), \operatorname{SumElim}\left(\lambda (i : \operatorname{Fin}\left(h\right)). \operatorname{z}\left(\operatorname{inl}\left(\operatorname{e}\left(\operatorname{inr}\left(i\right)\right)\right)\right), \lambda (i : \operatorname{Fin}\left(h\right)). \operatorname{z}\left(\operatorname{inr}\left(\operatorname{e}\left(\operatorname{inr}\left(i\right)\right)\right)\right)\right)\right)
$$

$$
\operatorname{matrix}\left(PiEquiv\right) = Pi
$$

$$
\operatorname{matrix}\left(\operatorname{symm}\left(PiEquiv\right)\right) = \operatorname{transpose}\left(Pi\right)
$$

$$
\operatorname{transpose}\left(Pi\right) \cdot Pi = 1
$$

$$
Pi \cdot \operatorname{transpose}\left(Pi\right) = 1
$$

$$
\operatorname{transpose}\left(Pi\right) \cdot Jb \cdot Pi = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right)
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(T\right) \cdot Pi\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot \operatorname{matrix}\left(T\right) \cdot Pi = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right)
$$

$$
\forall (a : (\operatorname{Fin}\left(r\right) \to \mathbb{R})), \operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(T\right)\right), \operatorname{mulVec}\left(\operatorname{transpose}\left(O\right), a\right)\right) = \operatorname{SumElim}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(B\right)\right), a\right), 0\right)
$$

$$
\forall (a : (\operatorname{Fin}\left(r\right) \to \mathbb{R})), \operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(T\right) \cdot Pi\right), \operatorname{mulVec}\left(\operatorname{transpose}\left(O\right), a\right)\right) = \operatorname{mulVec}\left(\operatorname{transpose}\left(Pi\right), \operatorname{SumElim}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(B\right)\right), a\right), 0\right)\right)
$$

The mode concatenation e sends a visible index to the first k entries and a hidden index to the following h entries, followed by the equality n=k+h. The index map iota sends block order (qv,pv,qh,ph) to global order (qv,qh,pv,ph). Pi is the 0/1 matrix with entry one exactly when iota(i)=j. It acts on coordinate functions by composition with iota. Reindexing the identity matrix proves both inverse identities and identifies the inverse linear equivalence's matrix with Pi-transpose. Reindexing Jplus gives Pi-transpose Jb Pi=Jplus_n. Transposing OT=[B,0] proves the covector identity for every a, and composition with Pi gives its permuted version.

### C8: the two exact Williamson applications and one final R

$$
\operatorname{Member}\left(Wv, \operatorname{symplecticGroup}\left(\operatorname{Fin}\left(k\right), \mathbb{R}\right)\right)
$$

$$
\operatorname{Member}\left(Wh, \operatorname{symplecticGroup}\left(\operatorname{Fin}\left(h\right), \mathbb{R}\right)\right)
$$

$$
\forall (i : \operatorname{Fin}\left(k\right)), 0 < \operatorname{nuv}\left(i\right)
$$

$$
\forall (i : \operatorname{Fin}\left(h\right)), 0 < \operatorname{nuh}\left(i\right)
$$

$$
\operatorname{transpose}\left(Wv\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(k\right), \mathbb{R}\right) \cdot Wv = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(k\right), \mathbb{R}\right)
$$

$$
\operatorname{transpose}\left(Wh\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(h\right), \mathbb{R}\right) \cdot Wh = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(h\right), \mathbb{R}\right)
$$

$$
\operatorname{transpose}\left(Wv\right) \cdot Sv \cdot Wv = Dv
$$

$$
\operatorname{transpose}\left(Wh\right) \cdot Sh \cdot Wh = Dh
$$

$$
\operatorname{matrix}\left(Bhat\right) = \operatorname{matrix}\left(B\right) \cdot Wv
$$

$$
\operatorname{matrix}\left(That\right) = \operatorname{matrix}\left(T\right) \cdot W
$$

$$
\forall (xv : (\operatorname{Sum}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right)\right) \to \mathbb{R})), \forall (xh : (\operatorname{Sum}\left(\operatorname{Fin}\left(h\right), \operatorname{Fin}\left(h\right)\right) \to \mathbb{R})), \operatorname{That}\left(\operatorname{SumElim}\left(xv, xh\right)\right) = \operatorname{mulVec}\left(Tv \cdot Wv, xv\right) + \operatorname{mulVec}\left(Th \cdot Wh, xh\right)
$$

$$
\operatorname{matrix}\left(R\right) = \operatorname{matrix}\left(That\right) \cdot Pi
$$

$$
\operatorname{range}\left(\operatorname{mulVecLin}\left(Tv \cdot Wv\right)\right) = \operatorname{range}\left(\operatorname{mulVecLin}\left(L\right)\right)
$$

$$
\operatorname{range}\left(\operatorname{mulVecLin}\left(Th \cdot Wh\right)\right) = \operatorname{ker}\left(\operatorname{mulVecLin}\left(O\right)\right)
$$

$$
Tv \cdot Wv = L \cdot \operatorname{matrix}\left(Bhat\right)
$$

$$
O \cdot \operatorname{matrix}\left(That\right) = \operatorname{columns}\left(\operatorname{matrix}\left(Bhat\right), 0\right)
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(That\right)\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot \operatorname{matrix}\left(That\right) = Jb
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(That\right)\right) \cdot S \cdot \operatorname{matrix}\left(That\right) = \operatorname{fromBlocks}\left(Dv, 0, 0, Dh\right)
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(R\right)\right) \cdot -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right) \cdot \operatorname{matrix}\left(R\right) = -\operatorname{MatrixJ}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right)
$$

$$
\operatorname{transpose}\left(\operatorname{matrix}\left(R\right)\right) \cdot S \cdot \operatorname{matrix}\left(R\right) = \operatorname{transpose}\left(Pi\right) \cdot \operatorname{fromBlocks}\left(Dv, 0, 0, Dh\right) \cdot Pi
$$

$$
\forall (a : (\operatorname{Fin}\left(r\right) \to \mathbb{R})), \operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(That\right)\right), \operatorname{mulVec}\left(\operatorname{transpose}\left(O\right), a\right)\right) = \operatorname{SumElim}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(Wv\right), \operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(B\right)\right), a\right)\right), 0\right)
$$

$$
\forall (a : (\operatorname{Fin}\left(r\right) \to \mathbb{R})), \operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(R\right)\right), \operatorname{mulVec}\left(\operatorname{transpose}\left(O\right), a\right)\right) = \operatorname{mulVec}\left(\operatorname{transpose}\left(Pi\right), \operatorname{SumElim}\left(\operatorname{mulVec}\left(\operatorname{transpose}\left(Wv\right), \operatorname{mulVec}\left(\operatorname{transpose}\left(\operatorname{matrix}\left(B\right)\right), a\right)\right), 0\right)\right)
$$

Apply the existing positive_definite_williamson separately to exactly Sv and Sh. Retain the actual returned Wv,Wh and strictly positive frequency functions nuv,nuh. Their symplectic membership gives invertibility, so the block map W is a linear equivalence. Define Bhat=BWv, That=TW, and R=That Pi as actual compositions of equivalences. Surjectivity of Wv and Wh preserves range Tv and range Th. Multiplication preserves TvWv=L Bhat and the observation identity. Block multiplication gives the exact two diagonal energy blocks, and the fixed Pi gives the displayed global energy. The final covector formula uses the transpose of this same R, not a separately chosen global Williamson map.

The bridge retains arbitrary n,r and empty/full endpoints. The existing Darboux, complement, permutation and Williamson constructions support empty finite indices; only the present strict-bound consumer concludes k,h>0. Covectors transform by R-transpose when z=Rx. No displacement transformation, physical implementation, metaplectic operator, tensor product, Gibbs state, or thermal assertion is part of the result.

## References

- Truth anchor: `D5/S3/QuadraticForms/OriginalDataCoupledCoordinates.original_data_coupled_coordinates`
- Dependency: [D5/S3/QuadraticForms/OriginalDataSymplecticSplit](OriginalDataSymplecticSplit.md)
- Dependency: [D5/S3/QuadraticForms/PositiveDefiniteWilliamson](PositiveDefiniteWilliamson.md)
