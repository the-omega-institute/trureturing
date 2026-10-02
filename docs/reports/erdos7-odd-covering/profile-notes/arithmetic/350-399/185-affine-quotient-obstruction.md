[Index](../../../marked_head_profile.md) · [Private-hull source](385-private-congruence-hulls-and-crossed-modulus-closure.md)

# An exact affine-quotient obstruction for a pair with no exact-two-owner points

Keep an EB1-selected whole cover with distinct odd numerical labels \(D\),
labelled classes \(A_m\), and minimum cardinality among all distinct odd
whole covers. Take distinct \(d,g\in D\) with

\[
 I:=A_d\cap A_g\ne\varnothing,\qquad
 L:=\operatorname{lcm}(d,g).
\]

Choose \(c\) with \(I=c+L\mathbb Z\). For every
\(h\in D\setminus\{d,g\}\) whose class meets \(I\), put

\[
 s_h:=\gcd(h,L),\qquad t_h:=h/s_h.
\tag{AQ1}
\]

The compatibility of the two congruences gives a unique residue
\(b_h\bmod t_h\) such that

\[
 (c+Lz)\in A_h
 \quad\Longleftrightarrow\quad
 z\equiv b_h\pmod {t_h}.
\tag{AQ2}
\]

The quotient modulus \(t_h\) is odd. The case \(t_h=1\) means that \(A_h\)
contains all of \(I\).

Define two obstructions:

* \(U_{d,g}\) holds if an active \(h\) has \(t_h=1\);
* \(Q_{d,g}\) holds if two active labels \(h_1,h_2\) have the same
  \(t_{h_1}=t_{h_2}>1\) but different quotient phases
  \(b_{h_1}\not\equiv b_{h_2}\pmod {t_{h_1}}\).

Then

\[
\boxed{
 K_{d,g}=\varnothing
 \quad\Longrightarrow\quad
 U_{d,g}\ \text{or}\ Q_{d,g}.
}
\tag{AQ3}
\]

Here \(K_{d,g}\) is the exact two-owner region from (RH3). Thus a
crowded intersection cannot be dismissed as an arbitrary higher-owner
phenomenon: in an extremal whole cover it must either be contained in one
third class, or carry a collision of induced quotient phases.

## Proof

Assume \(K_{d,g}=\varnothing\) and that neither \(U_{d,g}\) nor
\(Q_{d,g}\) holds. Every point of \(I\) has an owner other than \(d\) or
\(g\), so the active restrictions (AQ2) cover every \(z\in\mathbb Z\).
There is no active modulus \(1\), by the failure of \(U_{d,g}\). For each
odd \(t>1\), the failure of \(Q_{d,g}\) says that all active restrictions
with quotient modulus \(t\) have the same phase. Keep one copy of that
phase and discard the other labels. The resulting family is a finite
cover of \(\mathbb Z\) by distinct odd moduli \(t>1\), and it has at most
\(|D|-2\) classes. It is therefore a distinct odd whole cover strictly
smaller than the EB1-selected one, a contradiction. Hence (AQ3) holds.
\(\square\)

The argument uses one common source \(c+L\mathbb Z\) for all restrictions;
separately optimized quotient phases cannot be combined. It also uses only
cardinality minimality, not a modulus-sum comparison.

## Divisor-closure corollary

Suppose in addition that \(D\) is divisor-closed and every nonunit divisor
\(h>1\) of \(L\), other than \(d\) and \(g\), is comparable by divisibility
with at least one of \(d,g\). Then \(U_{d,g}\) is impossible in an
irredundant cover. Indeed, an active \(h\mid L\) has
\(A_h\cap I\ne\varnothing\). For comparable moduli, nonempty residue
classes are nested, so one of \(A_h,A_d,A_g\) contains another. The
contained class is redundant, contradicting the minimum-cardinality choice.
Consequently, under this shape condition,

\[
\boxed{
 K_{d,g}=\varnothing\quad\Longrightarrow\quad Q_{d,g}.
}
\tag{AQ4}
\]

For example, \(d=p^2\) and \(g=pq\), with distinct odd primes \(p,q\),
have \(L=p^2q\). Every nonunit divisor of \(L\) is comparable with one of
the two parents, so a missing exact-two-owner region for this pair forces a
same-quotient, different-phase collision. This does not assert that such a
collision is impossible; it identifies the precise remaining branch.

The finite crowded-star control in Section 8 of the cyclic CRT note realises the other
possibility in general: for \(d=15,g=21\), the divisor \(h=35\mid105\) can
contain their intersection without being comparable with either parent.
Thus the comparability hypothesis in (AQ4) is necessary and cannot be
silently dropped.

This obstruction is a new necessary condition on an unrestricted whole
cover. It does not force an exact-two-owner pair, eliminate all quotient
phase collisions, or settle Erdős #7; the remaining work is to pay or rule
out the \(U\)- and \(Q\)-branches using the original labels and phases.
