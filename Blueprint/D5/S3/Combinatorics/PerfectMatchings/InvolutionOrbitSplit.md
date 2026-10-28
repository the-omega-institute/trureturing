# Product Orbits of Two Perfect Matchings

## Abstract

Two fixed-point-free involutions split every matching component into two integer-power orbits of their product.

Let s and t be involutions of any type, and let r = s * t, with t applied first. Connectivity means a finite path of s-edges and t-edges. Rotation orbits use all integer powers of r and include singleton orbits. No finiteness or freeness of the rotation action is assumed. In the formulas Component(s,t,x) is the set of y connected to x; OrbitClasses(r,C) is the set of RotationOrbit(r,y) for y in C; PairSet(A,B) is {A,B}.

**Theorem 1.1 (Excluding Reflection Stabilizers).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Leftrightarrow \left(\forall k \in Int,\; \forall x \in X,\; \left(\left(s \cdot t\right)^{k} \cdot s\right)\left(x\right) \ne x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both generators have no fixed points exactly when every r^k s has no fixed points. For even k = 2j the reflection is conjugate to s by r^j; for odd k = 2j + 1 it is conjugate to t by r^(j+1). This covers negative exponents as well.

**Theorem 1.2 (The Matching Edge Separates Product Orbits).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Leftrightarrow \left(\forall x \in X,\; \neg \operatorname{SameCycle}\left(s \cdot t, x, s\left(x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_rotation_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both generators have no fixed points exactly when s(x) lies outside the r-orbit of x for every x. An intersection would give a reflection fixing x. Conversely, an s-fixed point violates separation at exponent zero, and a t-fixed point violates it at exponent one.

**Theorem 1.3 (Exact Alternating Reachability).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\forall x \in X,\; \forall y \in X,\; \operatorname{Connected}\left(s, t, x, y\right) \Leftrightarrow \left(\operatorname{SameCycle}\left(s \cdot t, x, y\right) \lor \operatorname{SameCycle}\left(s \cdot t, s\left(x\right), y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.connected_iff_rotation_orbits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary involutions, y is connected to x exactly when it lies in the r-orbit of x or in the r-orbit of s(x). Path induction gives the forward implication; positive and negative product powers give actual paths for the reverse implication. The two candidates may coincide when a generator has a fixed point.

**Theorem 1.4 (Disjoint Components and Matching Exchange).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Rightarrow \left(\forall x \in X,\; \operatorname{Disjoint}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right), \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \left(\operatorname{Component}\left(s, t, x\right) = \operatorname{Union}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right), \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \left(\operatorname{Image}\left(s, \operatorname{RotationOrbit}\left(s \cdot t, x\right)\right) = \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right) \land \operatorname{Image}\left(t, \operatorname{RotationOrbit}\left(s \cdot t, x\right)\right) = \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When both involutions have no fixed points, the two product orbits are nonempty and disjoint, and their union is precisely the matching component of x. The images of the first orbit under either s or t equal the second orbit; involutivity also exchanges them in the reverse direction.

**Theorem 1.5 (Exactly Two Product Orbit Classes).**

$$\forall X \in Type,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall t \in \operatorname{Perm}\left(X\right),\; \left(\left(\forall z \in X,\; s\left(s\left(z\right)\right) = z\right) \land \left(\forall z \in X,\; t\left(t\left(z\right)\right) = z\right)\right) \Rightarrow \left(\left(\left(\forall z \in X,\; s\left(z\right) \ne z\right) \land \left(\forall z \in X,\; t\left(z\right) \ne z\right)\right) \Rightarrow \left(\forall x \in X,\; \operatorname{OrbitClasses}\left(s \cdot t, \operatorname{Component}\left(s, t, x\right)\right) = \operatorname{PairSet}\left(\operatorname{RotationOrbit}\left(s \cdot t, x\right), \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right) \land \operatorname{RotationOrbit}\left(s \cdot t, x\right) \ne \operatorname{RotationOrbit}\left(s \cdot t, s\left(x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_orbit_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of all product orbits represented inside one matching component is precisely the pair of distinct orbits represented by x and s(x). If s = t, the product is the identity and each matching component still has two distinct singleton product orbits.

Application: corner cycles of arbitrary finitely paired triangles. Let F be any finite type of triangle occurrences. Write Side(F) = F × Fin(3), C = LocalCorner(F) = F × Fin(3), and X = Flag(F) = (F × Fin(3)) × Fin(2). A side (h,j) is opposite corner j of triangle h; a flag ((h,j),i) chooses endpoint i of that side. Although Side(F) and C have the same underlying product type, their entries have different incidence roles. A local corner retains its original triangle occurrence and corner number, even when several such corners acquire the same quotient vertex. Only finiteness of F is required; no enumeration, nonempty hypothesis, chosen group action, or orbit-coverage premise is supplied.

Pairing contract. The data q consist of pair : Side(F) → Side(F) and endpointTransport : Side(F) → Perm(Fin(2)), with the fields involutive, fixedPointFree, and compatible asserting, for every side u and endpoint i, pair(pair(u)) = u, pair(u) ≠ u, and endpointTransport(pair(u))(endpointTransport(u)(i)) = i. Thus every side has a distinct partner, and the endpoint permutations on partners are inverses. Either endpoint permutation on a side is allowed when this compatibility holds.

Endpoint table. Define sideCorner(j,i) by the following three rows; the entries in each row are the corner numbers at endpoints 0 and 1, in that order.

Side j = 0: (sideCorner(0,0), sideCorner(0,1)) = (1,2).

Side j = 1: (sideCorner(1,0), sideCorner(1,1)) = (2,0).

Side j = 2: (sideCorner(2,0), sideCorner(2,1)) = (0,1).

Set cornerAt((h,j),i) = (h,sideCorner(j,i)) and c((h,j),i) = cornerProjection((h,j),i) = cornerAt((h,j),i). The projection forgets which incident side was chosen but keeps the local corner occurrence.

Turn table. The entries in each row below are localTurn(j,0) and localTurn(j,1), respectively; each output is a (side number, endpoint number) pair.

Side j = 0: (localTurn(0,0), localTurn(0,1)) = ((2,1),(1,0)).

Side j = 1: (localTurn(1,0), localTurn(1,1)) = ((0,1),(2,0)).

Side j = 2: (localTurn(2,0), localTurn(2,1)) = ((1,1),(0,0)).

Supply mapping and product order. In this application choose s = turn and b = cross. The turn s preserves h and applies localTurn to (j,i); the crossing is b(u,i) = (pair(u),endpointTransport(u)(i)). Use these involutions as permutations s = turnEquiv and b = q.crossEquiv. In the owner statements above substitute the second generator t := b. Their product r is therefore p = s * b = turnEquiv * q.crossEquiv: crossing acts first, then turning. The two rows below will be p^i(f) and s(p^i(f)), with this same convention throughout.

Why the matching hypotheses hold. Applying b twice gives side pair(pair(u)) = u and endpoint endpointTransport(pair(u))(endpointTransport(u)(i)) = i, so b² = 1. A fixed flag for b would give pair(u) = u on first coordinates, contradicting fixedPointFree. The turn table consists of the three transpositions (0,0) ↔ (2,1), (0,1) ↔ (1,0), and (1,1) ↔ (2,0). Hence s² = 1 and s has no fixed flag. Each transposition preserves its sideCorner value, so c(s(x)) = c(x). The inverse of each flag permutation is itself; these are exactly the premises of the existing separation and component-splitting statements.

The exact projection fibers. Over corner (h,0) the flags are ((h,1),1) and ((h,2),0); over (h,1) they are ((h,0),0) and ((h,2),1); over (h,2) they are ((h,0),1) and ((h,1),0). These are all six entries of the endpoint table, grouped by their image. Equality c(x) = c(y) first forces equality of the triangle occurrences and then places the two local flags in one of these pairs. Consequently c(x) = c(y) if and only if y = x or y = s(x). The two flags in every fiber are distinct. This is a statement about equality of original local corners, before taking any quotient.

A concrete section proves surjectivity of c. Put cornerSection(h,k) = ((h,j(k)),1), where (j(0),j(1),j(2)) = (1,2,0). The endpoint table gives sideCorner(1,1) = 0, sideCorner(2,1) = 1, and sideCorner(0,1) = 2, so c(cornerSection(d)) = d for every d in C. No choice of a cyclic ordering or representative quotient vertex is hidden in this section.

The original corner quotient. Define q.cornerRel(u,v) to mean that some side w and endpoint i satisfy cornerAt(w,i) = u and cornerAt(pair(w),endpointTransport(w)(i)) = v. Equivalently define P(u,v) by ∃ x in X, c(x) = u and c(b(x)) = v; packing (w,i) into the flag x and unpacking it proves P = q.cornerRel in both directions. Let S = EqvGen(P), the smallest equivalence relation containing P: it admits generating edges, reflexive paths, reversed paths, and concatenations. Then Vertex(q) = Quotient(Relation.EqvGen.setoid(q.cornerRel)) and vertexClass(d) = Quotient.mk(d). For a flag f the required fiber is K_f = {d : C // vertexClass(d) = vertexClass(c(f))}. Its elements are local corner occurrences with an equality certificate, not the quotient vertices themselves.

From projected paths to flag paths. Put E(x,y) := (s(x) = y or b(x) = y) and R := EqvGen(E). The exact claim is S(c(f),c(g)) if and only if R(f,g), for any flags f and g. First ker(c) is contained in R: equal projections give either g = f, a reflexive path, or g = s(f), a single turn edge. This part of the argument uses only the fiber law.

For the lifting direction, let M(u,v) := ∃ x y, R(x,y) and c(x) = u and c(y) = v. This is Relation.Map R c c. Surjectivity of c and ker(c) contained in R make M an equivalence relation by Relation.map_equivalence. Concretely, surjectivity supplies reflexive witnesses, symmetry reverses an R-path, and in a composition the two lifts of the middle corner are R-related by the kernel inclusion. Every P-edge is in M, witnessed by x and b(x). Relation.EqvGen.mono and Equivalence.eqvGen_iff therefore give S contained in M. If S(c(f),c(g)), take the resulting witnesses x,y. The equalities c(x) = c(f) and c(y) = c(g) supply the endpoint adjustments f R x and y R g, and transitivity with x R y gives f R g. In particular, a projected edge lifts by adjusting within its first two-point fiber, crossing, and adjusting within its last fiber; these lifts join along every generated path.

For the projection direction, T(x,y) := S(c(x),c(y)) is an equivalence relation by Equivalence.comap. A crossing edge maps to P with witness x, and a turn edge maps to equality because c(s(x)) = c(x). Thus E is contained in T, and Relation.EqvGen.eqvGen_le gives R contained in T. This proves the claimed equivalence. The entire transport argument works for arbitrary functions s,b and a surjective c satisfying the same fiber law; it needs neither finiteness nor involutivity nor separation. Here its hypotheses have been established by the explicit triangle tables and section.

Equality in the actual vertex quotient now has an exact path interpretation: S(c(f),d) if and only if vertexClass(d) = vertexClass(c(f)). For the forward direction, Quotient.sound gives vertexClass(c(f)) = vertexClass(d), which we reverse. For the backward direction, reverse the displayed equality before applying Quotient.exact. This identifies the projected component with precisely K_f, retaining each underlying d unchanged.

Applying the existing two-orbit theorem. Since s and b are involutions, E is symmetric: an edge can be traversed backwards by the same generator. Relation.EqvGen.eqvGen_eq_reflTransGen therefore identifies R with the owner's reflexive-transitive matching connectivity; exchanging the order of the two alternatives in E makes no difference. Under t := b, connected_iff_rotation_orbits gives R(f,g) if and only if g belongs to Orbit_p(f) or Orbit_p(s(f)), where Orbit_p(x) = {p^k(x) : k in Int}. This coverage statement already holds for arbitrary involutions, without finiteness or fixed-point-freeness.

The second orbit is the turn row. The involution identities give s * p * s = p⁻¹, and hence s(p^k(f)) = p^(-k)(s(f)) for every integer k. Thus Orbit_p(s(f)) = s(Orbit_p(f)); equivalently p.SameCycle(s(f),g) if and only if p.SameCycle(f,s(g)). This is the sameCycle_conj and sameCycle_inv conversion in Mathlib. The component is therefore exactly the two rows p^k(f) and s(p^k(f)).

A pathwise reading makes the coverage concrete. The predicate A(z) := p.SameCycle(f,z) or p.SameCycle(f,s(z)) holds at f. A turn swaps its two alternatives since s² = 1. A crossing also swaps them: p(b(z)) = s(z) and s(b(z)) = p(z), and applying p does not change a SameCycle class. Hence A is preserved along either generator, and reflexivity, symmetry, and transitivity propagate it along every R-path. This explains the existing connected_iff_rotation_orbits supply on the present data; coverage is a conclusion, not an extra Pairing field.

Separation and exchange use the freeness already proved. The existing fixedPointFree_iff_rotation_separation, with s = turn and t = b = cross, gives ¬ p.SameCycle(z,s(z)) for every z. The component_split statement makes the two rows nonempty, disjoint, and exhaustive, and says that both generators exchange them. The component_orbit_classes statement identifies exactly these two distinct orbit classes. Crossing separation also has the exact required form ¬ p.SameCycle(z,b(z)): apply the same separation supply with generators (b,s), whose product b * s is p⁻¹, and use sameCycle_inv. Conversely, p(b(z)) = s(z) converts crossing separation to turn separation by sameCycle_apply_right. These are applications of the existing owner statements.

Positive minimal period. Fix a flag f. The finite type X and the injectivity of the permutation p make f periodic. Indeed, two terms of its infinite forward sequence coincide; cancelling the earlier power of p gives a positive return time. Write N = Function.minimalPeriod(p,f), the least positive n with p^n(f) = f. The Mathlib supplies Injective.mem_periodicPts and Function.minimalPeriod_pos_of_mem_periodicPts give N > 0. Define z_i = (p^(i : Nat))(f) for i in Fin(N), so the exponent is the natural value of the finite index.

Exact coordinates on one orbit. If y is in Orbit_p(f), SameCycle.exists_nat_pow_eq supplies k in Nat with p^k(f) = y. Set i = k mod N; positivity of N makes this an index in Fin(N), and Function.iterate_mod_minimalPeriod_eq gives z_i = y. Permutation powers are function iterates by Equiv.Perm.coe_pow. If z_i = z_j with i,j < N, Function.iterate_eq_iterate_iff_of_lt_minimalPeriod gives i = j. Thus the indices enumerate the entire product orbit exactly once, including a singleton orbit when N = 1.

Membership of the two rows does not need the involution hypotheses. For arbitrary permutations s,b, each forward step z → b(z) → s(b(z)) is an E-path from z to p(z). If π is the quotient map for EqvGen(E), these two edges give π(p(z)) = π(z). Function.iterate_invariant, Equiv.Perm.coe_pow, and Quotient.exact give R(f,p^k(f)) for every natural k. Appending a turn edge gives R(f,s(p^k(f))). This preserves the full generality of the forward-power membership argument; involutivity enters the exhaustive two-row description separately.

The finite two-row normal form is ν(i,0) = z_i and ν(i,1) = s(z_i), with (i,ε) in Fin(N) × Fin(2). Every such flag is R-connected to f by the preceding paths. Conversely, if R(f,y), the two-orbit supply gives either p.SameCycle(f,y) or p.SameCycle(f,s(y)). Reducing a natural power witness modulo N gives y = z_i in the first case; in the second it gives s(y) = z_i and hence y = s(z_i). Therefore ν covers the whole matching component.

The two-row normal form is also injective. Within row 0 use the minimal-period injectivity of z_i; within row 1 first cancel the permutation s and then use the same injectivity. An equality z_i = s(z_j) between different rows would put z_j and s(z_j) in Orbit_p(f), contrary to turn separation at z_j; the reversed mixed-row equality is treated by symmetry. Thus each connected flag has a unique pair (i,ε), and projecting forgets precisely ε because c(s(z_i)) = c(z_i).

The occurrence-fiber bijection. Define e : Fin(N) → K_f by e(i) = ⟨c(z_i), its vertex-class equality certificate⟩. This has the required type because R(f,z_i), projected-path transport, and Quotient.sound give vertexClass(c(f)) = vertexClass(c(z_i)); applying equality symmetry gives vertexClass(c(z_i)) = vertexClass(c(f)). Equivalently, each product step preserves the class: c(p(z)) = c(s(b(z))) = c(b(z)), and P relates c(z) to c(b(z)). Iterating these edges supplies the same certificate.

Injectivity of e is an assertion about original occurrences. If e(i) = e(j), equality of subtype values gives c(z_i) = c(z_j). The exact two-point fiber law gives either z_j = z_i or z_j = s(z_i). The first case forces i = j by the minimal-period bound. The second places a flag and its turn partner in one product orbit and contradicts separation. Equality of vertex-class certificates introduces no additional identifications of subtype values.

Surjectivity reaches every occurrence in K_f. Given d in K_f, choose y = cornerSection(d.val), so c(y) = d.val. First use d.property.symm, then apply Quotient.exact to obtain S(c(f),d.val); substituting c(y) and lifting the projected path gives R(f,y). The finite two-row normal form then gives y = z_i or y = s(z_i) for some i in Fin(N). In either case c(y) = c(z_i), so e(i) = d by subtype extensionality. The index is unique by injectivity, and choosing the other flag over d.val only exchanges the row tag. This proves surjectivity onto the full vertex fiber, with no assumption that quotient labels are injective.

The resulting equivalence has the exact forward formula e : Fin(Function.minimalPeriod(p,f)) ≃ {d : LocalCorner(F) // vertexClass(d) = vertexClass(c(f))}, with (e(i)).val = cornerProjection(((turnEquiv * q.crossEquiv)^(i : Nat))(f)). Here .val explicitly means the underlying local corner of the subtype. Equiv.ofBijective packages the proved map without changing it; alternatively one may first package the S-component and use Equiv.subtypeEquivRight with Quotient.sound/exact to change only the membership predicate. Both descriptions keep the displayed power coordinate on original occurrences.

In existential form, for every finite F, Pairing q, and flag f there are n in Nat with n > 0 and an equivalence e : Fin(n) ≃ K_f such that (e(i)).val = c((p^(i : Nat))(f)) for every i. The existential statement alone does not name the chosen n; the construction above specifically chooses n = Function.minimalPeriod(p,f). This is a complete application of the existing matching statements, relation-closure transport, and period-coordinate supplies, rather than a separate formalized theorem.

Degenerate and repeated incidences. N = 1 and N = 2 are included; the positive-period argument makes no lower-bound assumption beyond N > 0. Distinct sides of one triangle may be paired with one another, but a side occurrence cannot be paired with itself. Parallel pairings between triangle occurrences and repeated visits to the same triangle are allowed. Different local corners with the same vertex class remain different elements of K_f and receive different indices; repeated face or vertex labels impose no injectivity condition. Every side is paired, so this contract does not describe unpaired boundary sides. If F is empty, the pairing data are vacuous and X is empty: there is no input flag f and no asserted nonempty corner fiber. A supplied flag is what permits the positive-period construction.

Scope and supplies. The application concerns finite combinatorial incidence and the quotient of original corner occurrences. It supplies no geometric collar, saturation of a restricted geometric relation, disk or quotient homeomorphism, surface chart, global orientability, manifold theorem, surface classification, or Euler/genus formula. The matching coverage, separation, exchange, and orbit-class results are the existing InvolutionOrbitSplit statements above. The closure, quotient, and period steps use the named Mathlib supplies: Mathlib.Logic.Relation, Mathlib.GroupTheory.Perm.Cycle.Basic, Mathlib.Dynamics.PeriodicPts.Defs and Lemmas, Mathlib.Logic.Function.Iterate, Mathlib.Logic.Equiv.Defs, and Mathlib.Data.Quot. This application uses the owner source at revision 834c36f0b0500bef7f06c6c80af5e906e709ad44 and its Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_orbit_classes`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.component_split`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.connected_iff_rotation_orbits`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.fixedPointFree_iff_rotation_separation`
