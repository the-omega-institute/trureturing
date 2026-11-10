---
bibkey: mullerududec2012selfduality
authors: M. P. Müller and C. Ududec
year: 2012
title: The structure of reversible computation determines the self-duality of quantum theory
doi: 10.1103/PhysRevLett.108.130401
url: https://arxiv.org/abs/1110.3516v2
claim: Compact reversible bit symmetry yields a normalized invariant self-dualizing inner product in finite-dimensional general probabilistic theories.
strata_touched: []
license: citation-only
triage: anchor
---

# Bit symmetry and least proper confirmation effects

Theorem 1 of [arXiv:1110.3516v2](https://arxiv.org/pdf/1110.3516v2),
page 3, gives self-duality from bit symmetry. Its inner product is invariant
under the chosen compact reversible group, nonnegative on positive states,
has squared norm one on pure states, and makes perfectly distinguishable
states orthogonal. Page 2 defines bit symmetry as transitivity on ordered
pairs of perfectly distinguishable pure states. It is a requirement on
available reversible transformations, beyond symmetry of a numerical
comparison function. Odd regular polygons, including the pentagon, satisfy
the source's bit symmetry; this conclusion alone does not classify quantum
state spaces.

## Identification with the project's least proper effects

Use the finite-dimensional ordered carrier of
[the quantum-origin volume, Definition 26.1](../../docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md):
a nonzero real vector space $A$, a closed pointed generating cone $C$,
a strictly positive normalization $u$, the compact base
$K=\{x\in C:u(x)=1\}$, and the full proper-effect interval $[0,u]$.
Suppose the physical reversible group is compact and bit-symmetric. Suppose
also that each pure state $w$ has a **least** proper saturating effect:

$$
e_w\in[0,u],\qquad e_w(w)=1,\qquad
e_w\le f\quad\text{whenever }f\in[0,u],\ f(w)=1.
$$

Least means below every such effect in the dual-cone order; uniqueness of a
minimal element would be a different condition. Reciprocity and frame
spectrality are absent from these assumptions.

Apply the source theorem and call its inner product $B$. For pure $w$ put
$f_w=B(w,\cdot)$. If $s$ is pure, positivity and Cauchy–Schwarz give
$0\le B(w,s)\le1$. Every normalized mixed state is a finite convex
combination of pure states, so the same bound holds on $K$. Rescaling
positive vectors gives $0\le f_w\le u$, and $f_w(w)=1$. Full effect
availability therefore makes $f_w$ an admissible proper saturating effect.
This argument uses ordinary convex decompositions, not spectral
decompositions into distinguishable states; mixed states need not have
squared norm one.

Leastness gives $0\le e_w\le f_w$. By self-duality write
$e_w=B(v,\cdot)$ with $v\in C$, and put $r=w-v\in C$.
Saturation and symmetry give $B(w,r)=0$. Consequently

$$
0=B(w,r)=B(v,r)+B(r,r),\qquad
B(v,r)\ge0,\quad B(r,r)\ge0.
$$

Positive definiteness forces $r=0$. Hence

$$
e_w(x)=B(w,x),\qquad
e_w(s)=B(w,s)=B(s,w)=e_s(w).
$$

The cancellation step needs neither an extreme-ray lemma nor spectrality:
it holds whenever a positive functional is dominated by $B(w,\cdot)$ and
agrees with it at $w$. Pure states span $A$, so $w\mapsto e_w$ determines
this bilinear form and its linear state–effect identification uniquely.
The form is also invariant under the supplied reversible group. If $K$ is
a singleton, the generating assumption makes $A$ one-dimensional;
$B(aw,bw)=ab$ and $e_w=u$ give the conclusion directly.

This is an application of the cited self-duality theorem and elementary
inner-product positivity to the project's specified effect interval. It
does not claim a new general self-duality or transition-probability theorem.
In particular, the entire Müller–Ududec theorem is a literature premise,
not a theorem formalized here in Lean.

## What this removes and what it retains

In Definition 26.1, call least proper saturation alone $S_{\min}$.
The application gives

$$
S_{\min}+\text{compact physical bit symmetry}\ \Longrightarrow\ S.
$$

With the original signed frame spectrality Sp, Theorem 26.2 then supplies
the original three norm formulas. Bit symmetry alone supplies neither Sp
nor the all-frame strong symmetry needed for the Jordan classification.
Where the original strong symmetry is retained, it already includes
transitivity on two-element frames. The closure of its reversible group
inside the normalized-base automorphism group is compact and retains that
transitivity; using the closure in a geometric existence proof does not
declare its limit transformations physically callable.

Deleting the written reciprocity equality in that stronger context does
not enlarge the resulting model class. The more direct
[spectral strong-symmetry application](barnumhilgert2019spectral.md)
also makes leastness a consequence after Jordan classification. Neither
observation derives these stronger premises from a bare symmetric binary
function.

## Scope tests

The quantum-origin volume's Theorem 27.1 gives a useful boundary. For
$1<p<\infty$, the cone $C_p=\{(t,x):t\ge\|x\|_p\}$ has least proper
saturating effects and signed Sp. Its displayed reciprocity defect is
nonzero for $p\ne2$. Leastness and signed spectrality alone therefore do
not replace the missing dynamical condition.

Conversely, arbitrary proper saturating effects on an ordinary qubit need
not be reciprocal. For pure projectors $P,Q$ with
$c=\operatorname{Tr}(PQ)\in(0,1)$, choose
$E_P=P+t_P(I-P)$ and $E_Q=Q+t_Q(I-Q)$, where
$t_P,t_Q\in[0,1]$ and $t_P\ne t_Q$. Both effects saturate their own states,
but their cross-evaluations differ by $(t_P-t_Q)(1-c)$. Leastness identifies
the effects; self-duality does not identify an arbitrary assigned readout.

The upper bound in $[0,u]$ is essential to the meaning of this application.
For $P_0=|0\rangle\langle0|$ and
$P_\pm=|\pm\rangle\langle\pm|$, the positive operator $2P_-$ saturates
$P_0$ but evaluates to zero at $P_+$, whereas $P_0$ evaluates to $1/2$.
Thus leastness among proper saturating effects is different from leastness
among all positive saturating functionals. Transition-probability results
using the latter domain require their own hypotheses.

The geometry and reciprocity are compatible with classical simplices and
all simple Euclidean Jordan alternatives. They do not select the complex
field, specify a composite or instrument, or make sequential measurements
commute. The comparison $B(w,s)$ exchanges two endpoints of one relation;
it specifies no order of physical updates.
