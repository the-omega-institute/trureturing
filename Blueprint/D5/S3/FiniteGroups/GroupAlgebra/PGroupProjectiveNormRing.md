# A Split Norm Determines the Whole Representation

## Abstract

Split norms, coinduced modules and projective invariant coefficients over arbitrary commutative rings with nilpotent p.

Let p be prime, let a be positive, and let R be any commutative ring with (p : R)^a=0. Let P be a finite, possibly nonabelian p-group and V any R-module with a P-action. The ring may be zero; the group may be trivial; the module may be zero or arbitrarily generated. The coefficient ring, group and module have independent universes. Neither a field nor finite generation, finite presentation, locality, noetherianity or a nontriviality assumption is needed. All constructions use the actual invariant submodule and actual unnormalised norm.

Write A=R[P], I=ker(epsilon : A to R), J=pA and n=|P|. Coefficient reduction to R/pR gives I^n contained in J. The augmentation section r maps to r[1] gives I intersect J=JI without cancelling p, hence I^n contained in JI. The filtration I^(k(n-1)+1) contained in J^k I and J^a=0 give the improved bound I^(a(n-1)+1)=0. The imported augmentation_ideal_pow_pred_card supplies precisely this bound, including n=1 and the zero ring. No assertion of a minimal exponent is made.

Nilpotent augmentation detects a fixed vector in every module containing a supplied nonzero vector: choose the least ideal power annihilating that vector, and take a nonzero element from the preceding power acting on it. This element is killed by I, so each [g]-[1] kills it and it is P-invariant. The private helper exists_nonzero_mem_invariants_of_nilpotent_prime adapts the PGroupInvariants proof, reuses its arbitrary-semiring/module theorem exists_nonzero_killed_by_ideal, and transports through the actual asModuleEquiv. It is consumed on the actual kernel and actual quotient below. No finite-generation argument is involved. These are structural classical arguments, with utility none and no claim of literature novelty.

**Theorem 1.1 (A supplied norm section gives an equivariant linear equivalence).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact public telescope (universes uR uP uV): {R : Type uR} {P : Type uP} {V : Type uV} [CommRing R] [Group P] [Fintype P] [AddCommGroup V] [Module R V] (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (hp : (p : R) ^ a = 0) (hP : IsPGroup p P) (ρ : Representation R P V) (L : ρ.invariants →ₗ[R] V) (hL : ∀ w : ρ.invariants, ρ.norm (L w) = (w : V)) : ∃ E : V ≃ₗ[R] (P → ρ.invariants), ∀ (g h : P) (v : V), E (ρ g v) h = E v (h * g). The three universes are independent. The group may be nonabelian; V may be zero or arbitrarily generated. No field, finite-dimensionality, finite generation or presentation, locality, noetherianity, injectivity, coefficient projectivity of V, or projectivity or freeness of rho.invariants is assumed. Fintype P provides precisely the finite indexing needed by the actual norm.

Write W=rho.invariants and T_g(f)(h)=f(h*g). Associativity gives T_g T_a=T_(g*a), with the stated order valid for a nonabelian group. From the supplied ordinary R-linear section define the actual intertwining map Phi(f)=sum_g rho(g)L(f(g inverse)). Left-multiplication reindexing proves equivariance. For a constant function c(w), the section equation is Phi(c(w))=w as an underlying vector in V. Right-translation invariant functions are constant, by evaluating their invariance equations at the identity.

Injectivity uses the actual subrepresentation Phi.ker. If that kernel had a nonzero element, the private nilpotent-augmentation detector would supply a nonzero invariant element of the same kernel. Its underlying function is constant c(w), so Phi(c(w))=w=0 forces the function to be zero. This kills the actual kernel and proves Phi injective. It uses no dimension comparison or ordinary linear complement.

Surjectivity uses the actual range U=Phi.range and its actual quotient representation sigma=U.quotient on Q=V/U. Membership in U is exactly existence of a preimage under Phi. The quotient map pi satisfies sigma(g)pi(v)=pi(rho(g)v) and pi(v)=0 exactly when v belongs to U. If any vector were outside U, its class would be nonzero. The same private detector on Q would then give a nonzero sigma-fixed class c. Choose a lift m with pi(m)=c. Fixedness of c gives rho(g)m-m in U for every g. Choose its preimage a_g : P to W under Phi. Phi is injective, so applying Phi and expanding differences proves the crossed-homomorphism identity a_(g*h)=a_g+T_g(a_h). The calculation expands rho(g*h)m-m as (rho(g)m-m)+rho(g)(rho(h)m-m). Existence of these preimages comes from membership in the actual range; their uniqueness comes from the already-proved injectivity.

The cocycle is eliminated explicitly: set b(x)=a_x(1). The crossed-homomorphism identity with indices x,g, evaluated at 1, says b(x*g)=b(x)+a_g(x). Thus a_g(x)=b(x*g)-b(x), or a_g=T_g(b)-b. The equation rho(g)m-m=Phi(T_g(b))-Phi(b) gives rho(g)m-Phi(T_g(b))=m-Phi(b). Equivariance of Phi then makes m-Phi(b) fixed under rho. That fixed vector is Phi of its own constant invariant-valued function, hence lies in U. Phi(b) also lies in U, so m lies in U and c=pi(m)=0, contradicting its nonzero choice. This proves surjectivity. No unproved cohomology infrastructure, arbitrary-ring linear left inverse, or inference from containment of invariants alone is used.

The actual linear equivalence F=Phi is formed from its bijectivity, and E is its inverse. Injectivity of F transports its intertwining equation to the required right-translation equation for E. This completes the structural route with the exact supplied section hypothesis. Only the actual-kernel and actual-quotient fixed-vector detections use the p-group and p-nilpotence assumptions. Both feed through the new private helper and the exponent a*(Nat.card P-1)+1. The zero module, trivial group and zero ring use the same formulas; a supplied nonzero vector is the only nonzero input to detection.

**Theorem 1.2 (Projective invariant coefficients are the ring obstruction).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact public telescope (universes uR uP uV): {R : Type uR} {P : Type uP} {V : Type uV} [CommRing R] [Group P] [Fintype P] [AddCommGroup V] [Module R V] (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (hp : (p : R) ^ a = 0) (hP : IsPGroup p P) (ρ : Representation R P V) : Module.Projective R[P] ρ.asModule ↔ Module.Projective R ρ.invariants ∧ ∀ w : ρ.invariants, ∃ x : V, ρ.norm x = (w : V). The same independent universes and arbitrary-ring, arbitrary-module, finite possibly nonabelian p-group scope apply, under the positive exponent and nilpotent-p assumptions just displayed. Coefficient projectivity of V is a derived intermediate in one direction, never an additional assumption. The norm is the actual unnormalised Representation.norm, with no division by the group order.

Necessity first derives ordinary R-projectivity of V from group-algebra projectivity. The projective splitting property realizes rho.asModule as a retract of the free R[P]-module of rho.asModule-indexed finitely supported R[P]-valued functions. The standard MonoidAlgebra.basis P R shows R[P] is R-free; the Finsupp free-module instance shows that this same free cover is R-free. Restrict the two split maps to R using their actual scalar towers, apply Module.Projective.of_split, then transport through rho.asModuleEquiv. The restricted split maps use the compatible R and R[P] scalar actions. The free-module index is arbitrary and no universe equality or coefficient-projectivity hypothesis is required.

Still for necessity, form the actual intertwining orbit-cover q from right-translation functions P to V by q(f)=sum_g rho(g)f(g inverse). It is surjective because q(delta_1(v))=v. Convert q to an R[P]-linear map using Representation.IntertwiningMap.equivLinearMapAsModule and use the projective lifting property to split it. Convert the section back to an actual intertwining map S. If w is rho-invariant, S(w) is a right-translation invariant function and therefore constant. Define the ordinary R-linear map L(w)=S(w)(1); the split equation gives rho.norm(L(w))=w. Hence the actual norm surjects onto W and its codomain restriction Nbar : V to R-linear W satisfies Nbar composed with L equals the identity. Since V is now R-projective, Module.Projective.of_split makes W R-projective. This necessity argument is valid for every finite group over any commutative ring and uses neither p, a, ha, hp nor a p-group assumption. The coefficient-projectivity and norm-section helpers therefore have none of these parameters.

For sufficiency, R-projectivity of W splits the surjective actual norm with its codomain restricted to W, by Module.projective_lifting_property. The resulting R-linear section L satisfies exactly the hypothesis of the first theorem, which supplies the equivariant R-linear equivalence V with P to W. The remaining obligation is actual R[P]-projectivity of this function representation for projective W; it is fully implemented as follows.

Realize W as a retract of the free R-module of W-indexed finitely supported R-valued functions. Apply the split maps pointwise to obtain actual intertwining maps between the two right-translation function representations, then convert them to R[P]-linear maps with equivLinearMapAsModule. Their composite is the identity coordinate by coordinate. To show that functions with a free coefficient module M are R[P]-free, choose an arbitrary basis b of M indexed by an arbitrary type I. The basis-index universe is independent of the coefficient, group and module universes. Neither I nor M is assumed finite. The coordinate equivalence sends f to the I-indexed finitely supported family of group-algebra elements whose coefficient at a is b.repr(f(a inverse))(i). This inverse orientation turns right translation into the left regular action, including for nonabelian P.

The support conversion is explicit: apply the basis representation pointwise with inversion on P, convert only the finite P function coordinate to Finsupp, uncurry onto P times I, swap the product factors, curry onto I, and apply MonoidAlgebra.coeffLinearEquiv inversely in each coefficient. Finiteness is used only on P; there is no conversion of an arbitrary I-function to finite support. The coefficient identity proves an actual intertwining equivalence to Representation.free R P I; its actual free_asModule_free theorem supplies freeness over R[P]. Therefore the pointwise retract is R[P]-projective by of_split. Finally convert E to an R[P]-linear equivalence and transport projectivity back to rho.asModule. All free-module, function-module and projectivity transport helpers are consumed on this proof path.

The invariant-coefficient obstruction cannot be omitted over a ring. For example, with k a field of characteristic p, R=k[eta]/(eta^2), P=C_p and M=R[P]/eta R[P], the actual invariant module is k times the regular norm vector. The actual norm has the R-linear section sending that vector to [1], but M is not R[P]-projective: an R[P]-linear section of the quotient map R[P] to M would lift the class of 1 to 1+eta b, while linearity would require eta(1+eta b)=0, contradicting eta nonzero. The same argument shows R/(eta), hence the invariant coefficient module, is not R-projective. Thus a split norm still gives the first theorem without forcing projectivity. Over a field every invariant coefficient space is projective, even in arbitrary dimension, so the criterion reduces to norm-surjectivity. This is a consequence of the two displayed theorems, with no additional public specialization.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupAugmentationPrimePower](PGroupAugmentationPrimePower.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/PGroupInvariants](PGroupInvariants.md)
