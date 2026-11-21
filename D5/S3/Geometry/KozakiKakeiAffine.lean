/- GID: D5/S3/Geometry/KozakiKakeiAffine
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiAffine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Isolating an affine coordinate in each oriented matching product. -/
import D5.S3.Geometry.KozakiKakeiMatching
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace D5.S3.Geometry.KozakiKakei
open MvPolynomial
open scoped BigOperators
noncomputable section

abbrev Rest {V : Type*} (w : V) := {i : V // i ≠ w}
abbrev Coeff {V : Type*} (w : V) := MvPolynomial (Rest w) ℂ

def isolate {V : Type*} [DecidableEq V] (w : V) :
    MvPolynomial V ℂ ≃ₐ[ℂ] Polynomial (Coeff w) :=
  (renameEquiv ℂ (Equiv.optionSubtypeNe w).symm).trans (optionEquivLeft ℂ (Rest w))

@[simp] theorem isolate_X_self {V : Type*} [DecidableEq V] (w : V) :
    isolate w (X w) = Polynomial.X := by
  simp [isolate]

theorem isolate_X_other {V : Type*} [DecidableEq V] {w j : V} (hj : j ≠ w) :
    isolate w (X j) = Polynomial.C (X ⟨j, hj⟩) := by
  simp [isolate, Equiv.optionSubtypeNe_symm_of_ne hj]

theorem eval_isolate {V : Type*} [DecidableEq V] (w : V) (p : MvPolynomial V ℂ)
    (t : Rest w → ℂ) (z : ℂ) :
    eval (fun i => Option.elim ((Equiv.optionSubtypeNe w).symm i) z t) p =
      Polynomial.eval z (Polynomial.map (eval t) (isolate w p)) := by
  rw [isolate, AlgEquiv.trans_apply, renameEquiv_apply, ← optionEquivLeft_elim_eval, eval_rename]
  rfl

theorem diff_prime {V : Type*} {i j : V} (hij : i ≠ j) : Prime (diff i j) := by
  classical
  apply (MulEquiv.prime_iff (isolate j)).mp
  rw [diff, map_sub, isolate_X_self, isolate_X_other hij]
  exact Polynomial.prime_X_sub_C _

/-- Identifying one unordered pair does not kill the factor of a distinct pair. -/
theorem diff_not_dvd_of_edges_ne {V : Type*} {i j a b : V} (hab : a ≠ b)
    (hne : ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i))) :
    ¬ diff i j ∣ diff a b := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · intro hd
    have hz : diff a b = 0 := by simpa [diff] using hd
    have he := congrArg (eval (fun x => if x = a then 0 else 1 : V → ℂ)) hz
    simp [diff, hab.symm] at he
  let collapse : V → V := fun x => if x = j then i else x
  have hcollapse : collapse a ≠ collapse b := by
    intro h
    by_cases ha : a = j <;> by_cases hb : b = j
    · exact hab (ha.trans hb.symm)
    · exact hne (Or.inr ⟨ha, by simpa [collapse, ha, hb] using h.symm⟩)
    · exact hne (Or.inl ⟨by simpa [collapse, ha, hb] using h, hb⟩)
    · exact hab (by simpa [collapse, ha, hb] using h)
  let t : V → ℂ := fun x => if collapse x = collapse a then 0 else 1
  intro hd
  have he := map_dvd (eval t) hd
  have hsame : t i = t j := by simp [t, collapse, hij]
  have hb : t b = 1 := ite_eq_right hcollapse.symm
  have ha : t a = 0 := ite_eq_left rfl
  simp [diff, hsame, ha, hb] at he

private theorem matching_other_ne {m : ℕ} (M : Fin m × Bool ≃ Col m)
    {e i : Fin m} {b : Bool} (hi : i ≠ e) (c : Bool) : M (i, c) ≠ M (e, b) := by
  intro h
  exact hi (congrArg Prod.fst (M.injective h))

def remainingVertex {m : ℕ} (M : Fin m × Bool ≃ Col m) {e : Fin m} (b : Bool)
    (i : {i : Fin m // i ≠ e}) (c : Bool) : Rest (M (e, b)) :=
  ⟨M (i.val, c), matching_other_ne M i.property c⟩

def remainingProduct {m : ℕ} (M : Fin m × Bool ≃ Col m) (e : Fin m) (b : Bool) :
    Coeff (M (e, b)) :=
  ∏ i : {i : Fin m // i ≠ e}, diff (remainingVertex M b i false) (remainingVertex M b i true)

theorem eval_remainingProduct {m : ℕ} (M : Fin m × Bool ≃ Col m) (e : Fin m) (b : Bool)
    (t : Rest (M (e, b)) → ℂ) :
    eval t (remainingProduct M e b) =
      ∏ i : {i : Fin m // i ≠ e},
        (t (remainingVertex M b i true) - t (remainingVertex M b i false)) := by
  simp [remainingProduct, diff, map_prod]

private theorem matching_isolate {m : ℕ} (M : Fin m × Bool ≃ Col m)
    (e : Fin m) (b : Bool) :
    isolate (M (e, b)) (matchingPolynomial M) =
      (isolate (M (e, b)) (diff (M (e, false)) (M (e, true)))) *
        Polynomial.C (remainingProduct M e b) := by
  classical
  unfold matchingPolynomial remainingProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e), map_mul, map_prod, map_prod,
    Finset.prod_subtype (p := fun i => i ≠ e) (Finset.univ.erase e) (by simp)]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun i _ => ?_)
  simp only [diff, remainingVertex, map_sub, isolate_X_other (matching_other_ne M i.property false),
    isolate_X_other (matching_other_ne M i.property true)]

theorem matching_isolate_left {m : ℕ} (M : Fin m × Bool ≃ Col m) (e : Fin m) :
    isolate (M (e, false)) (matchingPolynomial M) =
      Polynomial.C (-(remainingProduct M e false)) * Polynomial.X +
        Polynomial.C (X ⟨M (e, true), by
          intro h
          have hh := congrArg Prod.snd (M.injective h)
          cases hh⟩ * remainingProduct M e false) := by
  have hn : M (e, true) ≠ M (e, false) := by
    intro h
    have hh := congrArg Prod.snd (M.injective h)
    cases hh
  rw [matching_isolate, diff, map_sub, isolate_X_self, isolate_X_other hn, map_neg, map_mul]
  ring

theorem matching_isolate_right {m : ℕ} (M : Fin m × Bool ≃ Col m) (e : Fin m) :
    isolate (M (e, true)) (matchingPolynomial M) =
      Polynomial.C (remainingProduct M e true) * Polynomial.X +
        Polynomial.C (-(X ⟨M (e, false), by
          intro h
          have hh := congrArg Prod.snd (M.injective h)
          cases hh⟩ * remainingProduct M e true)) := by
  have hn : M (e, false) ≠ M (e, true) := by
    intro h
    have hh := congrArg Prod.snd (M.injective h)
    cases hh
  rw [matching_isolate, diff, map_sub, isolate_X_self, isolate_X_other hn, map_neg, map_mul]
  ring

theorem matching_exists_linear {m : ℕ} (M : Fin m × Bool ≃ Col m) (w : Col m) :
    ∃ A B, isolate w (matchingPolynomial M) = Polynomial.C A * Polynomial.X + Polynomial.C B := by
  obtain ⟨⟨e, b⟩, rfl⟩ := M.surjective w
  cases b
  · exact ⟨_, _, matching_isolate_left M e⟩
  · exact ⟨_, _, matching_isolate_right M e⟩

theorem rename_matchingPolynomial {m : ℕ} (σ : Equiv.Perm (Col m))
    (M : Fin m × Bool ≃ Col m) :
    rename σ (matchingPolynomial M) = matchingPolynomial (M.trans σ) := by
  simp [matchingPolynomial, diff, map_prod]

theorem rename_F_exists_linear {m : ℕ} (σ : Equiv.Perm (Col m)) (w : Col m) :
    ∃ A B, isolate w (rename σ (F m)) = Polynomial.C A * Polynomial.X + Polynomial.C B := by
  obtain ⟨AE, BE, hE⟩ := matching_exists_linear ((evenMatching m).trans σ) w
  obtain ⟨AO, BO, hO⟩ := matching_exists_linear ((oddMatching m).trans σ) w
  refine ⟨AE - AO, BE - BO, ?_⟩
  rw [F, map_sub, rename_matchingPolynomial, rename_matchingPolynomial, map_sub,
    hE, hO, map_sub, map_sub]
  ring

#print axioms diff_prime
#print axioms diff_not_dvd_of_edges_ne
#print axioms rename_F_exists_linear

end
end D5.S3.Geometry.KozakiKakei
