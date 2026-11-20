# Caps of the unit quaternions and the causal order of the hyperboloid

## Abstract

Open caps of the unit quaternions with angular radius in (0, pi) correspond bijectively to the points of the one-sheeted hyperboloid |v|^2 - t^2 = 1 in R x H, a cap determines its centre and radius, and inclusion of caps is the causal order of the corresponding points.

**Definition 1.1 (The open cap with centre n and angular radius a).**

$$\forall n \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall a \in \mathbb{R},\; \operatorname{cap}\left(n, a\right) = \{ x \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \mid \operatorname{cos}\left(\frac{a}{2}\right)^{2} < \operatorname{kappa}\left(\operatorname{quaternionModel}, n, x\right) \}$$

*Formalization.* `D5/S3/Quantum/AURICOmega/CapCausalOrder.cap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a unit quaternion n and a real number a, the cap cap(n, a) is the set of unit quaternions x whose reading with n in the quaternion comparison model exceeds cos(a/2)^2. The reading is kappa(quaternionModel, n, x) = (1 + <n, x>) / 2 for the real inner product <n, x> of quaternions, and cos(a/2)^2 = (1 + cos(a)) / 2, so x lies in cap(n, a) exactly when cos(a) < <n, x>. For a in (0, pi) this is the open spherical cap of the unit three-sphere with centre n and angular radius a: the unit quaternions whose angle with n is less than a. The definition is made for every real a and depends on a only through cos(a). At the endpoint radii, a = pi gives the complement of the single point -n, because <n, x> > -1 fails only for x = -n, and a = 0 gives the empty set, because <n, x> <= 1 for unit quaternions.

**Definition 1.2 (The hyperboloid point of a cap).**

$$\forall n \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall a \in \mathbb{R},\; \operatorname{deSitterPoint}\left(n, a\right) = (-\frac{\operatorname{cos}\left(a\right)}{\operatorname{sin}\left(a\right)}, \operatorname{sin}\left(a\right)^{-1} \cdot n)$$

*Formalization.* `D5/S3/Quantum/AURICOmega/CapCausalOrder.deSitterPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

To a unit quaternion n and a real number a the definition attaches the pair (-cos(a)/sin(a), sin(a)^-1 n) of R x H, where n is viewed as a quaternion and sin(a)^-1 n is its real scalar multiple. For a in (0, pi) one has sin(a) > 0, and the identity sin(a)^-2 - cos(a)^2 / sin(a)^2 = 1 shows that the pair lies on the hyperboloid |v|^2 - t^2 = 1. Its first coordinate -cot(a) increases strictly with a on (0, pi), and its second coordinate points in the direction of the centre n. The theorem below uses the definition only for a in (0, pi).

**Theorem 1.3 (Caps, hyperboloid points and the causal order).**

$$\operatorname{BijOn}\left(p \mapsto \operatorname{deSitterPoint}\left(\operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right), \{ p \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right) \times \mathbb{R} \mid \operatorname{snd}\left(p\right) \in \operatorname{Ioo}\left(0, \pi\right) \}, \{ w \in \mathbb{R} \times \mathbb{H}[\mathbb{R}] \mid \left\lVert \operatorname{snd}\left(w\right) \right\rVert^{2} - \operatorname{fst}\left(w\right)^{2} = 1 \}\right) \land \left(\left(\forall n \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), m \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall a \in \mathbb{R}, b \in \mathbb{R},\; a \in \operatorname{Ioo}\left(0, \pi\right) \Rightarrow \left(b \in \operatorname{Ioo}\left(0, \pi\right) \Rightarrow \left(\operatorname{cap}\left(n, a\right) = \operatorname{cap}\left(m, b\right) \Leftrightarrow \left(n = m \land a = b\right)\right)\right)\right) \land \left(\forall n \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right), m \in \operatorname{unitary}\left(\mathbb{H}[\mathbb{R}]\right),\; \forall a \in \mathbb{R}, b \in \mathbb{R},\; a \in \operatorname{Ioo}\left(0, \pi\right) \Rightarrow \left(b \in \operatorname{Ioo}\left(0, \pi\right) \Rightarrow \left(\operatorname{cap}\left(n, a\right) \subseteq \operatorname{cap}\left(m, b\right) \Leftrightarrow \left(\operatorname{fst}\left(\operatorname{deSitterPoint}\left(n, a\right)\right) \le \operatorname{fst}\left(\operatorname{deSitterPoint}\left(m, b\right)\right) \land \left\lVert \operatorname{snd}\left(\operatorname{deSitterPoint}\left(m, b\right)\right) - \operatorname{snd}\left(\operatorname{deSitterPoint}\left(n, a\right)\right) \right\rVert^{2} \le \left(\operatorname{fst}\left(\operatorname{deSitterPoint}\left(m, b\right)\right) - \operatorname{fst}\left(\operatorname{deSitterPoint}\left(n, a\right)\right)\right)^{2}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/CapCausalOrder.cap_causal_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula the pair (n', a') is written (m, b), a centre and radius pair is written p with coordinates fst(p) and snd(p), and a point of R x H is written w. The theorem has three parts. First, the map sending a centre and a radius (n, a) to deSitterPoint(n, a) is a bijection from the pairs with a in (0, pi) onto the hyperboloid {(t, v) in R x H : |v|^2 - t^2 = 1}. Second, for radii a and a' in (0, pi), cap(n, a) = cap(n', a') holds exactly when n = n' and a = a'. Third, for radii a and a' in (0, pi), cap(n, a) is contained in cap(n', a') exactly when, writing (t, v) = deSitterPoint(n, a) and (t', v') = deSitterPoint(n', a'), one has t <= t' and |v' - v|^2 <= (t' - t)^2, that is, when the difference (t' - t, v' - v) lies in the closed future cone of the quadratic form t^2 - |v|^2 on R x H. The inverse of the point map sends (t, v) on the hyperboloid to the centre v / |v| and the radius arccos(-t / |v|); the hyperboloid equation forces |v| > 0 and (-t / |v|)^2 = 1 - |v|^-2 < 1, so the radius lies in (0, pi) and sin of the radius is |v|^-1. The second and third parts rest on one inclusion criterion: for a and a' in (0, pi), cap(n, a) is contained in cap(n', a') exactly when a <= a' and cos(a' - a) <= <n, n'>, equivalently when the angle between n and n' plus a is at most a'. If this holds, the triangle inequality for angles between unit vectors places every point of cap(n, a) at angle less than a' from n'. If it fails, choose a unit quaternion u orthogonal to n whose inner product with n' is minus the length of the component of n' orthogonal to n, and choose an angle b with 0 <= b < a, a' <= phi + b and phi + b <= pi, where phi is the angle between n and n'. The point x = cos(b) n + sin(b) u is a unit quaternion with <n, x> = cos(b) > cos(a), so x lies in cap(n, a), while <n', x> = cos(phi + b) <= cos(a'), so x does not lie in cap(n', a'). Equal caps contain each other, so the criterion gives a = a' and <n, n'> >= 1, which forces n = n' for unit quaternions. For the third part, -cot(a) <= -cot(a') holds exactly when a <= a', because cos(a') sin(a) - cos(a) sin(a') = sin(a - a'). Expanding both sides with |n| = |n'| = 1 and cot(a)^2 = sin(a)^-2 - 1 gives |v' - v|^2 = sin(a')^-2 + sin(a)^-2 - 2 <n, n'> / (sin(a) sin(a')) and (t' - t)^2 = sin(a')^-2 + sin(a)^-2 - 2 cos(a' - a) / (sin(a) sin(a')), so the second inequality is equivalent to cos(a' - a) <= <n, n'>. The restriction of the radii to (0, pi) cannot be dropped. The caps with a = pi, the complement of the point -n, and with a = 0, the empty set, do not correspond to points of the hyperboloid, since sin(a) = 0 there; and all caps of radius 0 coincide, so caps of radius 0 do not determine their centre. The statement concerns the hyperboloid as a subset of R x H and the displayed coordinate inequality between its points. A metric on the hyperboloid, its identification with de Sitter space and any physical reading of the causal condition are not part of the statement. The correspondence between oriented spheres of a sphere and the points of the one-sheeted hyperboloid, with inclusion of caps as the causal order, is classical in Möbius geometry; see for instance U. Hertrich-Jeromin, Introduction to Möbius Differential Geometry. Here the caps are defined through the reading of the quaternion comparison model on the unit quaternions.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/CapCausalOrder.cap`
- Truth anchor: `D5/S3/Quantum/AURICOmega/CapCausalOrder.cap_causal_order`
- Truth anchor: `D5/S3/Quantum/AURICOmega/CapCausalOrder.deSitterPoint`
- Dependency: [D5/S3/Quantum/AURICOmega/QuaternionComparisonModel](QuaternionComparisonModel.md)
