/- GID: D5/S3/Quantum/Fermionic/BcGhostBRST
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostBRST
   mirror-E: none(waiver:algebraic-ghost-brst-ward)
   anchors: []
   utility: none
   digest: Both Ward anticommutators of the actual locally finite cubic ghost charge. -/

import D5.S3.Quantum.Fermionic.BcGhostCubic

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostVirasoro (normal summand summand_finite L)
open private c_ket_tail c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

private theorem graph_finite (f : ℤ → Fock) (hf : Function.HasFiniteSupport f)
    (g : ℤ → ℤ) :
    Function.HasFiniteSupport (fun pq : ℤ × ℤ => if pq.2 = g pq.1 then f pq.1 else 0) := by
  apply (hf.image (fun p => (p, g p))).subset
  intro pq hpq
  by_cases hq : pq.2 = g pq.1
  · refine ⟨pq.1, ?_, ?_⟩
    · intro hz
      exact hpq (by simp [hq, hz])
    · exact Prod.ext rfl hq.symm
  · exact False.elim (hpq (by simp [hq]))

private theorem graph_sum (f : ℤ → Fock) (hf : Function.HasFiniteSupport f)
    (g : ℤ → ℤ) :
    (∑ᶠ pq : ℤ × ℤ, if pq.2 = g pq.1 then f pq.1 else 0) = ∑ᶠ p, f p := by
  rw [finsum_curry _ (graph_finite f hf g)]
  apply finsum_congr
  intro p
  rw [finsum_eq_single _ (g p) (fun q hq => by simp [hq])]
  simp

private theorem column_finite (f : ℤ → Fock) (hf : Function.HasFiniteSupport f)
    (a : ℤ) :
    Function.HasFiniteSupport (fun pq : ℤ × ℤ => if pq.1 = a then f pq.2 else 0) := by
  apply ((Set.finite_singleton a).prod hf).subset
  intro pq hpq
  by_cases hp : pq.1 = a
  · refine ⟨hp, ?_⟩
    intro hz
    exact hpq (by simp [hp, hz])
  · exact False.elim (hpq (by simp [hp]))

private theorem column_sum (f : ℤ → Fock) (hf : Function.HasFiniteSupport f)
    (a : ℤ) :
    (∑ᶠ pq : ℤ × ℤ, if pq.1 = a then f pq.2 else 0) = ∑ᶠ q, f q := by
  rw [finsum_curry _ (column_finite f hf a)]
  calc
    _ = ∑ᶠ p : ℤ, if p = a then ∑ᶠ q, f q else 0 := by
      apply finsum_congr
      intro p
      by_cases hp : p = a <;> simp [hp]
    _ = _ := by
      rw [finsum_eq_single _ a (fun p hp => by simp [hp])]
      simp

private theorem weighted_cubic_b (p q r : ℤ) (v : Fock) :
    cubicTerm (p,q) (b r v) + b r (cubicTerm (p,q) v) =
      (if q = -r then (1/2 : ℂ) • summand r p v else 0) +
      (if p = -r then (1/2 : ℂ) • summand r q v else 0) := by
  have h := LinearMap.congr_fun (cubic_b p q r) v
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [cubicTerm, LinearMap.smul_apply, map_smul, ← smul_add, h]
  by_cases hp : p = -r
  · subst p
    by_cases hq : q = -r
    · subst q
      simp [summand]
    · rw [show - -r-q = r-q by omega]
      simp [hq, show q+r ≠ 0 by omega, summand, smul_smul,
        Int.cast_sub, Int.cast_add, Int.cast_neg] <;> module
  · by_cases hq : q = -r
    · subst q
      rw [show -p- -r = r-p by omega]
      simp [hp, show p+r ≠ 0 by omega, summand, smul_smul,
        Int.cast_sub, Int.cast_add, Int.cast_neg] <;> module
    · simp [hp, hq, show p+r ≠ 0 by omega, show q+r ≠ 0 by omega]

/-- The full cubic anticommutator equals the actual supplier L, at every integer mode. -/
theorem ward_b (r : ℤ) : Qg * b r + b r * Qg = L r := by
  apply LinearMap.ext
  intro v
  have hv := cubicTerm_finite v
  have hw := cubicTerm_finite (b r v)
  have hmap := hv.fun_comp (map_zero (b r))
  let f : ℤ → Fock := fun p => (1/2 : ℂ) • summand r p v
  have hf : Function.HasFiniteSupport f :=
    (summand_finite r v).fun_comp (smul_zero (1/2 : ℂ))
  change (∑ᶠ pq : ℤ × ℤ, cubicTerm pq (b r v)) +
      b r (∑ᶠ pq : ℤ × ℤ, cubicTerm pq v) = _
  rw [map_finsum (b r) hv, ← finsum_add_distrib hw hmap]
  calc
    _ = ∑ᶠ pq : ℤ × ℤ,
        ((if pq.2 = -r then f pq.1 else 0) +
        (if pq.1 = -r then f pq.2 else 0)) := by
      apply finsum_congr
      intro pq
      exact weighted_cubic_b pq.1 pq.2 r v
    _ = (∑ᶠ pq : ℤ × ℤ, if pq.2 = -r then f pq.1 else 0) +
        (∑ᶠ pq : ℤ × ℤ, if pq.1 = -r then f pq.2 else 0) :=
      finsum_add_distrib (graph_finite f hf (fun _ => -r)) (column_finite f hf (-r))
    _ = (∑ᶠ p, f p) + (∑ᶠ p, f p) := by
      rw [graph_sum f hf (fun _ => -r), column_sum f hf (-r)]
    _ = L r v := by
      dsimp only [f]
      rw [← smul_finsum' (1/2 : ℂ) (summand_finite r v)]
      change (1/2 : ℂ) • L r v + (1/2 : ℂ) • L r v = L r v
      module

private theorem cc_ket_finite (r : ℤ) (S : Finset ℕ) :
    Function.HasFiniteSupport (fun p : ℤ => (c p * c (r-p)) (ket S)) := by
  let A : ℤ := (S.sup id + 3 : ℕ)
  apply (Set.finite_Icc (r-A) A).subset
  intro p hp
  have h₁ : p ≤ A := by
    by_contra hn
    have hz : c p (ket S) = 0 := c_ket_tail p S (by dsimp [A] at hn; omega)
    exact hp (by simp [c_swap p (r-p), Module.End.mul_apply, hz])
  have h₂ : r-p ≤ A := by
    by_contra hn
    have hz : c (r-p) (ket S) = 0 := c_ket_tail (r-p) S (by dsimp [A] at hn; omega)
    exact hp (by simp [Module.End.mul_apply, hz])
  exact ⟨by omega, h₁⟩

/-- The constrained pure-c quadratic is locally finite on every original state. -/
theorem cc_finite (r : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun p : ℤ => (c p * c (r-p)) v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [Function.HasFiniteSupport, Function.support]
  | add f g hf hg =>
    apply (hf.union hg).subset
    intro p hp
    by_contra hn
    have hpf : (c p * c (r-p)) f = 0 := by
      by_contra hz
      exact hn (Or.inl hz)
    have hpg : (c p * c (r-p)) g = 0 := by
      by_contra hz
      exact hn (Or.inr hz)
    exact hp (by simp only [map_add, hpf, hpg, add_zero])
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs]
    simp only [map_smul]
    exact (cc_ket_finite r S).fun_comp (smul_zero a)

def rTerm (r p : ℤ) : Module.End ℂ Fock :=
  ((1/2 : ℂ) * ((2*p-r : ℤ) : ℂ)) • (c p * c (r-p))

theorem rTerm_finite (r : ℤ) (v : Fock) :
    Function.HasFiniteSupport (fun p : ℤ => rTerm r p v) := by
  apply (cc_finite r v).subset
  intro p hp hn
  exact hp (by simp [rTerm, hn])

/-- The full pure-c Ward operator, with p+q=r and no truncation hypothesis. -/
def R (r : ℤ) : Module.End ℂ Fock where
  toFun v := ∑ᶠ p : ℤ, rTerm r p v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (rTerm_finite r v) (rTerm_finite r w)
  map_smul' a v := by
    simp only [map_smul]
    exact (smul_finsum' a (rTerm_finite r v)).symm

private theorem weighted_cubic_c (p q r : ℤ) (v : Fock) :
    cubicTerm (p,q) (c r v) + c r (cubicTerm (p,q) v) =
      if q = r-p then rTerm r p v else 0 := by
  have h := LinearMap.congr_fun (cubic_c p q r) v
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  simp only [cubicTerm, LinearMap.smul_apply, map_smul, ← smul_add, h]
  by_cases hq : q = r-p
  · subst q
    simp only [show -p-(r-p)+r = 0 by omega, if_true, rTerm,
      LinearMap.smul_apply]
    congr 2
    push_cast
    ring
  · simp [show -p-q+r ≠ 0 by omega, hq]

/-- The second exact Ward anticommutator on the countable algebraic Fock space. -/
theorem ward_c (r : ℤ) : Qg * c r + c r * Qg = R r := by
  apply LinearMap.ext
  intro v
  have hv := cubicTerm_finite v
  have hw := cubicTerm_finite (c r v)
  have hmap := hv.fun_comp (map_zero (c r))
  change (∑ᶠ pq : ℤ × ℤ, cubicTerm pq (c r v)) +
      c r (∑ᶠ pq : ℤ × ℤ, cubicTerm pq v) = _
  rw [map_finsum (c r) hv, ← finsum_add_distrib hw hmap]
  calc
    _ = ∑ᶠ pq : ℤ × ℤ, if pq.2 = r-pq.1 then rTerm r pq.1 v else 0 := by
      apply finsum_congr
      intro pq
      exact weighted_cubic_c pq.1 pq.2 r v
    _ = R r v := graph_sum _ (rTerm_finite r v) (fun p => r-p)

end D5.S3.Quantum.Fermionic.BcGhostBRST
