# FIB strict-real joint incidence: overlap-stratified finite response lifts

## 1. The four-endpoint relation and its overlap index

Use the complete fixed-terminal inverse and the same-base relation from
\`FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X\`, especially Definition 6.3.
Thus \(p\ne24\), the two \(J\)-endpoints \(W_0,W_1\) have independently
chosen terminal values \(m_0,m_1\), and the two \(M\)-endpoints \(W_2,W_3\)
have the common terminal value \(m\). The within-pair conditions are

$$
W_0\ne W_1,\qquad W_2\ne W_3.
$$

Define the cross-pair overlap index

$$
\boxed{\kappa
=\left|\{W_0,W_1\}\cap\{W_2,W_3\}\right|}
\in\{0,1,2\}.
$$

For each endpoint write

$$
\tau_i\in\{O,E\},
$$

according as \(W_i\) is reconstructed from the ordinary layer
\(\mathcal R(p,v,m_i)\) or the exceptional layer
\(\mathcal E(p,v,m_i)\), with \(m_2=m_3=m\). Equal worlds have equal
labels and equal terminal values. This label records the inverse chart used
to count the endpoint; it does not add a new source or relax any strict
guard.

The purpose of \(\kappa\) is only to stratify the unresolved relation. It
does not assert that any stratum is nonempty.

## 2. The overlap-stratified lift

**Proposition 2.1 (Finite response lift by overlap stratum).** Fix
\((p,v)\) with \(p\ne24\) and a solution of Definition 6.3. Then:

1. If \(\kappa=2\), the unordered endpoint sets coincide. Consequently
   \(m_0=m_1=m\). After fixing \((p,v,m)\), the number of ordered
   four-endpoint realizations in this stratum is at most

   $$
   4\binom{7}{2}=2\cdot7\cdot6=84.
   $$

2. If \(\kappa=1\), there are indices \(i\in\{0,1\}\) and
   \(j\in\{2,3\}\) with \(W_i=W_j\). Hence \(m_i=m\), while the other
   \(J\)-terminal \(m_{1-i}\) remains independent. After fixing
   \((p,v,m,m_{1-i})\), the number of ordered four-endpoint realizations
   with this specified shared-slot pair is at most

   $$
   7\cdot6\cdot7=294,
   $$

   and allowing the four choices of \((i,j)\) gives the uniform bound

   $$
   4\cdot7\cdot6\cdot7=1176.
   $$

3. If \(\kappa=0\), all four endpoints are distinct. After fixing the
   complete response tuple \((p,v,m_0,m_1,m)\), the number of ordered
   four-endpoint realizations is at most

   $$
   7^4=2401.
   $$

The corresponding response-coordinate projections are respectively

$$
\begin{array}{c|c}
\kappa & \text{response coordinates}\\ \hline
2 & (p,v,m),\\
1 & (p,v,m,m_{1-i}),\\
0 & (p,v,m_0,m_1,m).
\end{array}
$$

Thus the endpoint multiplicity is finite in every stratum; it cannot by
itself contribute an additional continuous response coordinate.

**Proof.** By Theorem 5.2 of the preceding continuation, every fixed
\((p,v,q)\) fibre

$$
\mathcal R(p,v,q)\sqcup\mathcal E(p,v,q)
$$

has at most seven worlds. If an exceptional layer is present, it has at
most two worlds and the ordinary layer at most five.

When \(\kappa=2\), two two-element sets with intersection of size two are
equal. Every world in the \(M\)-pair has terminal value \(m\), while every
world in the \(J\)-pair has its assigned terminal value \(m_0\) or \(m_1\).
Equality of the two sets therefore forces \(m_0=m_1=m\). Choose the two
distinct worlds from a fibre of size at most seven and order them for the
\(J\)-pair and \(M\)-pair independently. This gives
\(4\binom72=84\).

When \(\kappa=1\), choose the shared \(J\)-slot \(i\) and \(M\)-slot \(j\).
The shared world lies in the \(m\)-fibre, and the other \(M\)-slot must be a
different world in that fibre, giving at most \(7\cdot6\) choices. The
other \(J\)-slot lies in the fibre with terminal value \(m_{1-i}\), giving
at most seven choices. There are four choices for the pair \((i,j)\). If
\(m_{1-i}=m\), this product is only a uniform upper bound; the distinctness
conditions can reduce it further.

When \(\kappa=0\), each endpoint is chosen from one of the three fixed
terminal fibres, each of cardinality at most seven. Multiplying the four
bounds gives \(7^4\). The within-pair inequalities only reduce this count.

The coordinate statements are exactly the terminal equalities forced in
the first two cases and the independent choices allowed in the third.
The ordinary/exceptional refinement follows by replacing each factor seven
with the cardinality of its selected layer. \(\square\)

## 3. Ordinary/exceptional refinements

For \(q\in\mathbb R\), set

$$
c_O(p,v,q)=|\mathcal R(p,v,q)|,\qquad
c_E(p,v,q)=|\mathcal E(p,v,q)|.
$$

Theorem 5.2 gives

$$
c_E(p,v,q)\le2,
$$

and, whenever \(c_E(p,v,q)>0\),

$$
c_O(p,v,q)\le5;
$$

otherwise \(c_O(p,v,q)\le7\). For a fixed type vector
\(\tau=(\tau_0,\tau_1,\tau_2,\tau_3)\), the corresponding raw endpoint
count is bounded by

$$
\prod_{i=0}^{3}c_{\tau_i}(p,v,m_i),
\qquad m_2=m_3=m.
$$

In the \(\kappa=2\) stratum, equal endpoints also require equal type
labels. In the \(\kappa=1\) stratum, the shared pair has the same label,
and the remaining labels are unconstrained except by their own layer
membership. These are finite-count refinements of Proposition 2.1; they do
not assert that every \(O/E\) pattern occurs.

## 4. What this does and does not settle

The proposition supplies a faithful finite-fibre lift of the unresolved
four-endpoint relation. It separates the only three possible overlap
patterns and prevents the fixed-\((p,v,m)\) bound seven from being applied
to the independent \(m_0,m_1,m\) problem. It also identifies the precise
coordinate reduction available in the fully overlapping stratum: only
\((p,v,m)\) remains continuous there.

It does not construct a point of \(D_J\cap D_M\), prove that any overlap
stratum is nonempty, or prove a global absence theorem. It does not infer
that the number of response coordinates is a physical space dimension,
that a semialgebraic dimension equals the displayed coordinate count, or
that raw or complex lifts are strict-real witnesses. The remaining joint
question still ranges over ordinary/exceptional mixtures, repeated roots,
degree drops, zero drift, sampled gain zeros, and singular sources exactly
as in Definition 6.5 of the preceding continuation.

The result is a combinatorial reduction over the exact real inverse. Its
role is to turn a single unstructured search into three finite-fibre
strata; a subsequent exact or exclusion argument must still address the
actual equality of the \(J\)-responses and the independently chosen
\(M\)-pair.

## 追加锚（本行以下为增补区）
