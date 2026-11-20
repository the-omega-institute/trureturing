/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSWeightedDehomogenization
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSWeightedDehomogenization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization]
   utility: none
   digest: Dehomogenization in a weight-one variable preserves relative primality. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization
import Mathlib.RingTheory.Localization.FractionRing

/-! A common factor in an affine chart would homogenize to a common factor
of the original equations. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedDehomogenization

open MvPolynomial

open private degreeExpansion degreeExpansion_monomial degreeExpansion_coeff
  degreeExpansion_ne_zero weight_le_expansion_degree
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization

noncomputable section

variable {σ K : Type*} [Field K]

private abbrev R := MvPolynomial σ K
private abbrev S := MvPolynomial (Option σ) K

/-- Set the distinguished weight-one variable to one. -/
def dehom : S (σ := σ) (K := K) →+* R (σ := σ) (K := K) :=
  eval₂Hom C (fun j => j.elim 1 X)

/-- Substitution by polynomials of the prescribed weights preserves a
homogeneous component, including when some weights are zero. -/
theorem eval₂Hom_homogeneous {τ L : Type*} [CommSemiring L] (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ L) (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    {p : MvPolynomial σ L} {n : ℕ} (hp : p.IsWeightedHomogeneous w n) :
    (eval₂Hom C f p).IsWeightedHomogeneous v n := by
  classical
  nth_rw 1 [MvPolynomial.as_sum p]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [eval₂Hom_monomial, Finsupp.prod, ← hp (mem_support_iff.mp hm)]
  have h := IsWeightedHomogeneous.prod m.support (fun j => f j ^ m j)
    (fun j => m j • w j) (fun j _ => (hf j).pow (m j))
  simpa only [Finsupp.weight_apply, Finsupp.sum, zero_add] using
    (isWeightedHomogeneous_C v (p.coeff m)).mul h

theorem rename_homogeneous {τ : Type*} (e : σ ≃ τ) (w : σ → ℕ)
    {p : R (σ := σ) (K := K)} {n : ℕ} (hp : p.IsWeightedHomogeneous w n) :
    (renameEquiv K e p).IsWeightedHomogeneous (w ∘ e.symm) n := by
  have he : (renameEquiv K e).toRingHom = eval₂Hom C (X ∘ e) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [renameEquiv_apply]
    · intro i
      simp [renameEquiv_apply, Function.comp_def]
  change ((renameEquiv K e).toRingHom p).IsWeightedHomogeneous (w ∘ e.symm) n
  rw [he]
  apply eval₂Hom_homogeneous w _ _ _ hp
  intro i
  simpa [Function.comp_def] using isWeightedHomogeneous_X K (w ∘ e.symm) (e i)

theorem dehom_homogeneous_of_weight_zero (w : σ → ℕ) {p : S (σ := σ) (K := K)} {n : ℕ}
    (hp : p.IsWeightedHomogeneous (fun j => j.elim 0 w) n) :
    (dehom p).IsWeightedHomogeneous w n := by
  apply eval₂Hom_homogeneous (fun j => j.elim 0 w) _ _ _ hp
  rintro (_ | j)
  · simpa using isWeightedHomogeneous_C w (1 : K)
  · exact isWeightedHomogeneous_X K w j

private def embed (w : σ → ℕ) : S (σ := σ) (K := K) →+* Polynomial (R (σ := σ) (K := K)) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun j => Polynomial.C (j.elim 1 X) * Polynomial.X ^ j.elim 1 w)

private lemma expansion_degree (w : σ → ℕ) (p : R (σ := σ) (K := K)) :
    (degreeExpansion w p).natDegree = p.weightedTotalDegree w := by
  classical
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [degreeExpansion_coeff]
    exact weightedHomogeneousComponent_eq_zero n p hn
  · exact Finset.sup_le fun _ hd => weight_le_expansion_degree w hd

private lemma weighted_degree_mul (w : σ → ℕ) {p q : R (σ := σ) (K := K)}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).weightedTotalDegree w = p.weightedTotalDegree w + q.weightedTotalDegree w := by
  rw [← expansion_degree w, map_mul, Polynomial.natDegree_mul
    (degreeExpansion_ne_zero w hp) (degreeExpansion_ne_zero w hq), expansion_degree,
    expansion_degree]

private lemma embed_monomial (w : σ → ℕ) (d : Option σ →₀ ℕ) (c : K) :
    embed w (monomial d c) =
      Polynomial.C (dehom (monomial d c)) *
        Polynomial.X ^ Finsupp.weight (fun j => j.elim 1 w) d := by
  classical
  unfold embed dehom
  rw [eval₂Hom_monomial, eval₂Hom_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum, Polynomial.C_mul, mul_assoc]
  congr 2
  apply congrArg (fun n : ℕ => (Polynomial.X : Polynomial (MvPolynomial σ K)) ^ n)
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _

private lemma embed_homogeneous (w : σ → ℕ) {p : S (σ := σ) (K := K)} {n : ℕ}
    (hp : p.IsWeightedHomogeneous (fun j => j.elim 1 w) n) :
    embed w p = Polynomial.C (dehom p) * Polynomial.X ^ n := by
  classical
  nth_rw 1 [MvPolynomial.as_sum p]
  rw [map_sum]
  calc
    _ = ∑ d ∈ p.support, Polynomial.C (dehom (monomial d (p.coeff d))) *
        Polynomial.X ^ n := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [embed_monomial, hp (mem_support_iff.mp hd)]
    _ = _ := by
      rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← MvPolynomial.as_sum p]

private lemma embed_injective (w : σ → ℕ) :
    Function.Injective (embed (K := K) w) := by
  let P := MvPolynomial (Option σ) K
  let Q := FractionRing P
  let i : P →+* Q := algebraMap P Q
  let t := i (X none)
  have ht : t ≠ 0 := by
    change i (X none) ≠ 0
    intro h
    apply X_ne_zero (R := K) (none : Option σ)
    exact IsFractionRing.injective P Q (h.trans (map_zero i).symm)
  let f : MvPolynomial σ K →+* Q := eval₂Hom (i.comp C)
    (fun k => i (X (some k)) / t ^ w k)
  let F := Polynomial.eval₂RingHom f t
  have h : F.comp (embed w) = i := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [F, embed, f]
    · rintro (_ | j)
      · simp [F, embed, f, t]
      · simp [F, embed, f, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
  intro a b hab
  apply IsFractionRing.injective P Q
  have he : (F.comp (embed w)) a = (F.comp (embed w)) b := congrArg F hab
  rw [h] at he
  exact he

set_option maxHeartbeats 800000 in
-- The degree estimate expands a weighted polynomial as a sum of evaluated monomials.
private lemma dehom_degree_le (w : σ → ℕ) {p : S (σ := σ) (K := K)} {n : ℕ}
    (hp : p.IsWeightedHomogeneous (fun j => j.elim 1 w) n) :
    (dehom p).weightedTotalDegree w ≤ n := by
  classical
  rw [← expansion_degree w]
  unfold dehom
  rw [map_eval₂Hom]
  change (p.eval₂ ((degreeExpansion w).comp C)
    (fun j => degreeExpansion w (j.elim 1 X)) :
      Polynomial (MvPolynomial σ K)).natDegree ≤ n
  rw [eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  let a : Option σ → Polynomial (MvPolynomial σ K) :=
    fun j => degreeExpansion w (j.elim 1 X)
  have ha (j : Option σ) : (a j).natDegree ≤ j.elim 1 w := by
    cases j with
    | none => simp [a]
    | some j =>
      simp only [a, Option.elim_some]
      rw [degreeExpansion, eval₂Hom_X']
      exact Polynomial.natDegree_mul_le.trans (by simp)
  have hC (c : K) : (degreeExpansion w (C c)).natDegree = 0 := by
    rw [degreeExpansion, eval₂Hom_C, RingHom.comp_apply]
    exact Polynomial.natDegree_C _
  calc
    _ ≤ (∏ j ∈ d.support, a j ^ d j).natDegree := by
      simpa only [hC, zero_add, a, RingHom.comp_apply] using (Polynomial.natDegree_mul_le
        (p := degreeExpansion w (C (p.coeff d))) (q := ∏ j ∈ d.support, a j ^ d j))
    _ ≤ ∑ j ∈ d.support, (a j ^ d j).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ d.support, d j * j.elim 1 w := Finset.sum_le_sum fun j _ =>
      Polynomial.natDegree_pow_le_of_le _ (ha j)
    _ = n := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id] using
        hp (mem_support_iff.mp hd)

private def homLift (w : σ → ℕ) (p : R (σ := σ) (K := K)) (n : ℕ) : S (σ := σ) (K := K) :=
  ∑ d ∈ p.support, rename some (monomial d (p.coeff d)) *
    (X none) ^ (n - Finsupp.weight w d)

private lemma embed_homLift (w : σ → ℕ) (p : R (σ := σ) (K := K)) (n : ℕ)
    (hn : p.weightedTotalDegree w ≤ n) :
    embed w (homLift w p n) = Polynomial.C p * Polynomial.X ^ n := by
  classical
  unfold homLift
  rw [map_sum]
  have he (q : R (σ := σ) (K := K)) : embed w (rename some q) = degreeExpansion w q := by
    exact eval₂Hom_rename _ _ _ _
  have hX : embed (K := K) w (X none) = Polynomial.X := by simp [embed]
  calc
    ∑ d ∈ p.support, embed w (rename some (monomial d (p.coeff d)) *
        X none ^ (n - Finsupp.weight w d)) =
        ∑ d ∈ p.support, Polynomial.C (monomial d (p.coeff d)) * Polynomial.X ^ n := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [map_mul, map_pow, he, hX, degreeExpansion_monomial,
        ← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add,
        Nat.add_sub_of_le ((le_weightedTotalDegree w hd).trans hn)]
    _ = _ := by rw [← Finset.sum_mul, ← map_sum, ← MvPolynomial.as_sum p]

private lemma dehom_embed_at_one (w : σ → ℕ) (p : S (σ := σ) (K := K)) :
    (embed w p).eval 1 = dehom p := by
  have h : (Polynomial.evalRingHom 1).comp (embed (K := K) w) = dehom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [embed, dehom]
    · rintro (_ | j) <;> simp [embed, dehom]
  exact RingHom.congr_fun h p

/-- Specializing the distinguished variable of weight one does not erase a
nonzero weighted-homogeneous polynomial. -/
theorem dehom_ne_zero (w : σ → ℕ) {p : S (σ := σ) (K := K)} {n : ℕ}
    (hp : p ≠ 0) (hP : p.IsWeightedHomogeneous (fun j => j.elim 1 w) n) : dehom p ≠ 0 := by
  intro he
  exact hp (embed_injective w (by rw [embed_homogeneous w hP, he, map_zero, zero_mul, map_zero]))

/-- Specialization of a weight-one variable to one preserves relative
primality of two nonzero homogeneous polynomials. -/
theorem relatively_prime_dehom (w : σ → ℕ) {p q : S (σ := σ) (K := K)} {m n : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : IsRelPrime p q)
    (hP : p.IsWeightedHomogeneous (fun j => j.elim 1 w) m)
    (hQ : q.IsWeightedHomogeneous (fun j => j.elim 1 w) n) :
    IsRelPrime (dehom p) (dehom q) := by
  classical
  intro f hfp hfq
  have hpn := dehom_ne_zero w hp hP
  have hqn := dehom_ne_zero w hq hQ
  let d := f.weightedTotalDegree w
  let F := homLift w f d
  have hF : embed w F = Polynomial.C f * Polynomial.X ^ d := embed_homLift w f d le_rfl
  have lift_dvd (r : S (σ := σ) (K := K)) (k : ℕ)
      (hr : r.IsWeightedHomogeneous (fun j => j.elim 1 w) k)
      (hrn : dehom r ≠ 0) (hfr : f ∣ dehom r) : F ∣ r := by
    obtain ⟨g, hg⟩ := hfr
    have hf₀ : f ≠ 0 := fun e => hrn (by rw [hg, e, zero_mul])
    have hg₀ : g ≠ 0 := fun e => hrn (by rw [hg, e, mul_zero])
    have hdeg := dehom_degree_le w hr
    rw [hg, weighted_degree_mul w hf₀ hg₀] at hdeg
    have hgle : g.weightedTotalDegree w ≤ k - d := by dsimp [d]; omega
    refine ⟨homLift w g (k - d), embed_injective w ?_⟩
    rw [embed_homogeneous w hr, hg, map_mul (embed w), hF, embed_homLift w g _ hgle,
      mul_mul_mul_comm, ← map_mul, ← pow_add, Nat.add_sub_of_le (by dsimp [d]; omega)]
  have hunit : IsUnit F := h (lift_dvd p m hP hpn hfp) (lift_dvd q n hQ hqn hfq)
  have he := dehom_embed_at_one w F
  rw [hF, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, mul_one] at he
  exact he ▸ hunit.map dehom

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedDehomogenization
