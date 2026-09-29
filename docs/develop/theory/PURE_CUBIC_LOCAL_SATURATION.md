# Local saturation of a pure-cubic order

This volume uses the cubic order of
`PURE_CUBIC_INTEGRAL_LATTICES.md`, Section 3. It isolates a local
maximality statement that does not require the whole radicand to be
squarefree.

## 1. Saturation at a simple prime divisor

**Theorem 1.1 (simple-prime saturation).** Let $a$ be an integer and let
$K$ be a characteristic-zero field with a rational power basis
$(1,\theta,\theta^2)$ of dimension three. Suppose
$\theta^3=B=1+9a$, and set

$$
\beta=\frac{1+\theta+\theta^2}{3},\qquad
A=\mathbb Z\cdot1+\mathbb Z\cdot\theta+\mathbb Z\cdot\beta.
$$

Let $p$ be a positive prime satisfying $p\mid B$ and $p^2\nmid B$.
For every $z\in K$ integral over $\mathbb Z$,

$$
pz\in A\quad\Longrightarrow\quad z\in A.
$$

Proof. The polynomial $X^3-B$ is the minimal polynomial of $\theta$
over $\mathbb Z$. Its nonleading coefficients are divisible by $p$,
and its constant coefficient is not divisible by $p^2$, so it is
Eisenstein at $p$. Multiplying $pz\in A$ by $3$ puts $p(3z)$ in
$\mathbb Z[\theta]$, since $3\beta=1+\theta+\theta^2$. The element
$3z$ is integral. The Eisenstein integrality criterion therefore puts
$3z$ in $\mathbb Z[\theta]\subseteq A$. Section 5 of the cited volume
proves that $A$ is saturated at $3$ among integral elements; hence
$z\in A$.

## 2. Boundary and source

The conclusion concerns one prime with valuation exactly one in $B$.
It does not identify the full ring of integers when some other prime
square divides $B$, or compute a field discriminant or normalization
index. The proof combines the pinned Mathlib Eisenstein integrality
criterion with the three-saturation theorem in
`PURE_CUBIC_INTEGRAL_LATTICES.md`; the local statement is a
repository-derived extension of that volume's squarefree case.

## 追加锚（本行以下为增补区）
