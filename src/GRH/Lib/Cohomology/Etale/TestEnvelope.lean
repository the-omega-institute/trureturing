import GRH.Lib.Cohomology.Etale.TestRings
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Functorial envelope: maps from given rings to tests factor through a test ring. -/

open CategoryTheory Classical CommRingCat MvPolynomial Ideal.Quotient
variable (B) {W V J : Type} [CommRing B] [CommRing W] [CommRing V] (g : W →+* V)

namespace Envelope

/-- x solves equation o with coefficients a: x idempotent, a₀ ∣ xa₁, a₁ ∣ (1 − x)a₀ (o = 0); a₀ⁿ
∣ a_{n+1} − x for all n (o = 1); Σ_{k<n} a_k x^k = 0 (o = n + 2). -/
def IsSolution (a : ℕ → V) x | 0 => IsIdempotentElem x ∧ a 0 ∣ x * a 1 ∧ a 1 ∣ (1 - x) * a 0
                             | 1 => ∀ n, a 0 ^ n ∣ a (n + 1) - x | n + 2 => ∑ k ∈ .range n,
                               a k * x ^ k = 0

/-- Formal names for solutions over B: a term is an equation number o with a sequence of
coefficients, each a polynomial over B in finitely many earlier terms. -/
inductive SolutionName
  | op (o : ℕ) (n : ℕ → ℕ) (P : ∀ k, MvPolynomial (Fin (n k)) B) (t : ∀ k, Fin (n k) → SolutionName)

/-- g: W → V is injective, and every equation `Envelope.IsSolution` with coefficients in g(W)
that has a solution in V has one in g(W). -/
def IsSolutionClosed := (⇑g).Injective ∧ ∀ o a, (∃ x, IsSolution (g ∘ a) x o) → ∃ x,
  IsSolution (g ∘ a) (g x) o

variable {B g}

/-- Every ring map φ: B → V extends to a ring map g from the polynomial ring
over B such that the induced injection of its quotient by ker g into V satisfies the closure
condition `Envelope.IsSolutionClosed`. -/
lemma exists_isSolutionClosed φ : ∃ g : MvPolynomial (SolutionName B) B →+* V, g.comp C = φ ∧
  IsSolutionClosed g.kerLift := ⟨eval₂Hom φ
  (·.rec fun o _ P _ v ↦ epsilon (IsSolution (P · |>.eval₂ φ (v _)) · o)), by simp,
  RingHom.kerLift_injective _, fun _ ↦ mk_surjective.comp_left.forall.2 fun a h ↦ by
  choose n t _ P e using (a · |>.exists_fin_rename)
  exact ⟨mk _ (X (.op ..)), by simpa [e, eval₂_rename, Function.comp_def] using epsilon_spec h⟩⟩

lemma IsSolutionClosed.map_dvd_iff (h : IsSolutionClosed g) {x y} : g x ∣ g y ↔ x ∣ y :=
  ⟨by simpa [← h.1.eq_iff, dvd_def, IsSolution,
  Finset.sum_range, neg_add_eq_zero] using (h.2 4 ([-y].getD · x)), map_dvd g⟩

/-- If a ring map g: W → V satisfies the closure condition `Envelope.IsSolutionClosed` and V is a
test ring, then W is a test ring. -/
lemma IsSolutionClosed.isTest (h : IsSolutionClosed g) : IsTest V → IsTest W
  | ⟨a, c, _⟩ => ⟨⟨fun P m d ↦ by simpa [P.eval_eq_sum_range, ← h.1.eq_iff] using! (h.2 (_ + 3)
    _ (by simpa [P.eval₂_eq_sum_range] using! a.exists_eval₂_eq_zero g m d))⟩,
    fun x y ↦ by simpa [← h.map_dvd_iff, ← h.1.eq_iff, IsIdempotentElem] using!
    (h.2 0 ([x].getD · y) (c ..)), isReduced_of_injective g h.1⟩

/-- For any family of commutative rings R_o, there are an endofunctor E of commutative rings
with every E(A) a test ring and a natural map θ: A → E(A) such that every homomorphism from
an R_o to a test ring factors through θ at R_o. -/
lemma exists_functorial_test (R : J → _) : ∃ E, ∃ θ : 𝟭 CommRingCat ⟶ E, (∀ A, IsTest (E A)) ∧
  ∀ o (A : TestRing) φ, ∃ ψ : _ ⟶ A.1, θ (R o) ≫ ψ =
  φ := let e {S} := Pi.evalRingHom fun x : Σ q : {q : Σ o, Ideal
    (MvPolynomial (SolutionName (R o)) (R o)) // IsTest (_ ⧸ q.2)}, S ⟶ of (_ ⧸ q.1.2) ↦ _ ⧸ x.1.1.2
  ⟨.mk _ fun f ↦ ofHom (.pi (e ⟨_, f ≫ ·.2⟩)), .mk fun _ ↦ ofHom (.pi (·.2.1)),
        fun _ ↦ .pi (·.1.2), fun _ A φ ↦ (exists_isSolutionClosed φ.1).elim fun g h ↦
    ⟨ofHom (g.kerLift.comp (e ⟨⟨⟨_, _⟩, h.2.isTest A.2⟩, ofHom (algebraMap ..)⟩)), hom_ext h.1⟩⟩
