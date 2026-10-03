/- GID: D5/S3/Quantum/SpinChains/HypereclecticNonShortening
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/HypereclecticNonShortening
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Powers of the one-wall hypereclectic Hamiltonian have maximal rank between levels. -/

/-
result:
  proof_shape: content
  escape_witness: lowering_kernel_zero_aux proves sharp weight-space injectivity
    by induction on the remaining raising length, with the dual giving surjectivity.
  admission_basis: open-problem-resolution (#12310; Proved)
Direct frozen dependencies:
  D5/S1/Words/ParityCode/OddTopWeight.ones
    (statement_id: sha256:1d9174a721063a3dbe5b6c8b0cb36c7298a9dd4e2f46f0071d686bd8eefff654)
Private theorem classification:
  weight_eq_level: content; inversion-count induction on the bin length.
  localR_localH_commute, positional_telescope and wordSl2: bind-only;
    inlined as local facts in their consuming proofs.
  lowering_kernel_zero_aux: content; induction on the raising length, using
    the primitive-vector chain nonvanishing theorem at the terminal vector.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.ParityCode.OddTopWeight
import Mathlib.Algebra.Lie.Sl2

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open scoped BigOperators
open Module
open D5.S1.Words.ParityCode.OddTopWeight (ones)

attribute [local instance] LieRing.ofAssociativeRing

namespace D5.S3.Quantum.SpinChains.HypereclecticNonShortening

def level {N : ℕ} (w : (Fin N → Bool)) : ℕ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j ∧ w i = true ∧ w j = false then 1 else 0

def sector (L M : ℕ) : Set ((Fin (L - 1) → Bool)) := {w | ones w = M - 1}

def W (L M S : ℕ) : Submodule ℚ (((Fin (L - 1) → Bool) → ℚ)) :=
  Submodule.span ℚ ((Pi.basisFun ℚ ((Fin (L - 1) → Bool))) '' {w | w ∈ sector L M ∧ level w = S})

private def localH {N : ℕ} (a b : Fin N) : Module.End ℚ (((Fin N → Bool) → ℚ)) := by
  exact {
    toFun v w := if w a = false ∧ w b = true then v (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) else 0
    map_add' v u := by
      ext w
      by_cases hc : w a = false ∧ w b = true <;> simp [hc]
    map_smul' c v := by
      ext w
      by_cases hc : w a = false ∧ w b = true <;> simp [hc]
  }

private def localR {N : ℕ} (a b : Fin N) : Module.End ℚ (((Fin N → Bool) → ℚ)) := localH b a

private def Hbin (N : ℕ) : Module.End ℚ (((Fin N → Bool) → ℚ)) :=
  ∑ p : Fin (N - 1), localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))

def H (L _M : ℕ) : Module.End ℚ (((Fin (L - 1) → Bool) → ℚ)) := Hbin (L - 1)

private def Rbin (N : ℕ) : Module.End ℚ (((Fin N → Bool) → ℚ)) :=
  ∑ p : Fin (N - 1), (((p : ℕ) + 1 : ℚ) * ((N : ℚ) - ((p : ℕ) + 1))) •
    localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))

private def weight {N : ℕ} (w : (Fin N → Bool)) : ℚ :=
  ∑ i : Fin N, if w i then (N : ℚ) - 1 - 2 * (i : ℕ) else 0

private theorem weight_eq_level {N : ℕ} (w : (Fin N → Bool)) :
    weight w = 2 * (level w : ℚ) - (ones w : ℚ) * ((N : ℚ) - ones w) := by
  induction N with
  | zero => simp [weight, level, ones]
  | succ N ih =>
    let u : (Fin N → Bool) := fun i => w i.castSucc
    have hb : ones w = ones u + (if w (Fin.last N) then 1 else 0) := by
      simp only [ones, Fin.sum_univ_castSucc]
      rfl
    have hs : level w = level u + (if w (Fin.last N) then 0 else ones u) := by
      simp only [level, Fin.sum_univ_castSucc]
      have hl : ∀ i : Fin (N + 1), ¬ Fin.last N < i := by
        intro i
        exact not_lt_of_ge (Fin.le_last i)
      simp only [hl, false_and, if_false, Finset.sum_const_zero, add_zero,
        Fin.castSucc_lt_last, true_and, Fin.castSucc_lt_castSucc_iff]
      cases hw : w (Fin.last N) <;> simp [hw, u, level, ones, Finset.sum_add_distrib]
    have hg : weight w = weight u + (ones u : ℚ) -
        (if w (Fin.last N) then (N : ℚ) else 0) := by
      rw [weight, Fin.sum_univ_castSucc]
      have hm : (∑ i : Fin N, if w i.castSucc then
          (N + 1 : ℕ) - (1 : ℚ) - 2 * (i.castSucc : ℕ) else 0) =
          weight u + (ones u : ℚ) := by
        simp only [weight, ones, Nat.cast_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        cases hw : w i.castSucc <;> simp [u, hw] <;> ring
      rw [hm]
      cases hw : w (Fin.last N) <;> simp [hw] <;> ring
    rw [hg, hb, hs, ih]
    cases hw : w (Fin.last N) <;> simp [hw, Nat.cast_add] <;> ring

def restrict (L M S k : ℕ) : W L M S →ₗ[ℚ] W L M (S - k) := by
  have localH_apply {N : ℕ} (a b : Fin N) (v : ((Fin N → Bool) → ℚ)) (w : (Fin N → Bool)) :
      localH a b v w = if w a = false ∧ w b = true then v (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) else 0 := rfl
  have twos_swap {N : ℕ} (a b : Fin N) (w : (Fin N → Bool)) :
      ones (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) = ones w := by
    simp only [ones, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap]
    exact Equiv.sum_comp (Equiv.swap a b) (fun i => if w i then 1 else 0)
  have mem_W_iff (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) :
      v ∈ W L M S ↔ ∀ w, v w ≠ 0 → ones w = M - 1 ∧ level w = S := by
    rw [W, (Pi.basisFun ℚ ((Fin (L - 1) → Bool))).mem_span_image]
    simp [Set.subset_def, sector, Finsupp.mem_support_iff]
  have weighted_swap {N : ℕ} (δ : Fin N → ℚ) (w : (Fin N → Bool))
      (a b : Fin N) (hab : a ≠ b) :
      (∑ i : Fin N, if ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w i then δ i else 0) -
        (∑ i : Fin N, if w i then δ i else 0) =
        (δ a - δ b) * ((if w b then 1 else 0) - (if w a then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib]
    let f (i : Fin N) : ℚ :=
      (if ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w i then δ i else 0) - (if w i then δ i else 0)
    change ∑ i : Fin N, f i = _
    rw [← Finset.sum_erase_add Finset.univ f (a := a) (Finset.mem_univ a)]
    rw [← Finset.sum_erase_add (Finset.univ.erase a) f (a := b) (by simp [hab.symm])]
    have hz : ∑ i ∈ (Finset.univ.erase a).erase b, f i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hia : i ≠ a := by simpa using (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hib : i ≠ b := (Finset.mem_erase.mp hi).1
      simp [f, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hia hib]
    rw [hz, zero_add]
    cases hwa : w a <;> cases hwb : w b <;>
      simp [f, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, hwa, hwb] <;> ring
  have weight_swap_edge {N : ℕ} (p : Fin (N - 1)) (w : (Fin N → Bool))
      (hleft : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false) (hright : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true) :
      weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = weight w + 2 := by
    have hab : ((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) ≠ ((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) := by
      intro he
      have := congrArg Fin.val he
      dsimp only at this
      omega
    have he := weighted_swap (fun i : Fin N => (N : ℚ) - 1 - 2 * (i : ℕ)) w
      (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) hab
    change weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) - weight w =
      (((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) : Fin N) : ℕ)) -
        ((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) : Fin N) : ℕ))) *
        ((if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) then 1 else 0) - (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) then 1 else 0)) at he
    simp only [hleft, hright, Bool.false_eq_true, if_false, if_true, sub_zero, mul_one] at he
    have hc : (((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) : Fin N) : ℕ)) -
        ((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) : Fin N) : ℕ))) = 2 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hc] at he
    linarith
  have level_swap_edge {N : ℕ} (p : Fin (N - 1)) (w : (Fin N → Bool))
      (hleft : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false) (hright : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true) :
      level (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = level w + 1 := by
    have hw := weight_swap_edge p w hleft hright
    have ht := twos_swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) w
    rw [weight_eq_level, weight_eq_level, ht] at hw
    have he : (level (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) : ℚ) = (level w : ℚ) + 1 := by
      linarith
    exact_mod_cast he
  have H_mem_W (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) (hv : v ∈ W L M S) :
      H L M v ∈ W L M (S - 1) := by
    rw [mem_W_iff] at hv ⊢
    intro w hw
    have hp : ∃ p : Fin ((L - 1) - 1),
        localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) v w ≠ 0 := by
      by_contra! hn
      apply hw
      simp only [H, Hbin, LinearMap.sum_apply, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro p hpi
      exact hn p
    obtain ⟨p, hp⟩ := hp
    have hc : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true := by
      by_contra hn
      apply hp
      simp [localH_apply, hn]
    rw [localH_apply, if_pos hc] at hp
    have hv' := hv (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) hp
    have ht := twos_swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) w
    have hs := level_swap_edge p w hc.1 hc.2
    constructor
    · rw [← ht]
      exact hv'.1
    · omega
  have H_pow_mem_W (L M S k : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) (hv : v ∈ W L M S) :
      (H L M ^ k) v ∈ W L M (S - k) := by
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      have he := H_mem_W L M (S - k) ((H L M ^ k) v) ih
      simpa only [Nat.sub_sub] using he
  exact
    ((H L M ^ k).comp (W L M S).subtype).codRestrict (W L M (S - k))
      (fun v => H_pow_mem_W L M S k v v.property)


def claim : Prop := ∀ L M : ℕ, 1 ≤ M → M ≤ L → ∀ S k : ℕ, k ≤ S →
  Module.finrank ℚ (LinearMap.range (restrict L M S k)) =
    min (Module.finrank ℚ (W L M S)) (Module.finrank ℚ (W L M (S - k)))

private def projectToW (L M S : ℕ) : ((Fin (L - 1) → Bool) → ℚ) →ₗ[ℚ] W L M S := by
  have mem_W_iff (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) :
      v ∈ W L M S ↔ ∀ w, v w ≠ 0 → ones w = M - 1 ∧ level w = S := by
    rw [W, (Pi.basisFun ℚ ((Fin (L - 1) → Bool))).mem_span_image]
    simp [Set.subset_def, sector, Finsupp.mem_support_iff]
  have projectW_apply (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) (w : (Fin (L - 1) → Bool)) :
      (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v w = if ones w = M - 1 ∧ level w = S then v w else 0 := by
    simp only [LinearMap.mulLeft_apply, Pi.mul_apply, ite_mul, one_mul, zero_mul]
  have projectW_mem (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) : (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v ∈ W L M S := by
    rw [mem_W_iff]
    intro w hw
    by_contra hn
    apply hw
    simp [projectW_apply, hn]
  exact
    ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0))).codRestrict (W L M S) (projectW_mem L M S)


private theorem lowering_kernel_zero_aux {V : Type} [AddCommGroup V] [Module ℚ V]
    {g r h : Module.End ℚ V} (t : IsSl2Triple g r h) (n : ℕ) :
    ∀ (v : V) (q k : ℕ), g v = (q : ℚ) • v → k ≤ q →
      (r ^ n) v = 0 → (h ^ k) v = 0 → v = 0 := by
  have lower_pow_raise {V : Type} [AddCommGroup V] [Module ℚ V]
      {g r h : Module.End ℚ V} (t : IsSl2Triple g r h) {v : V} {μ : ℚ}
      (hv : g v = μ • v) (k : ℕ) :
      (h ^ (k + 1)) (r v) = r ((h ^ (k + 1)) v) -
        (((k + 1 : ℕ) : ℚ) * (μ - k)) • ((h ^ k) v) := by
    induction k with
    | zero =>
      have ht := congrArg (fun f : Module.End ℚ V => f v) t.lie_e_f
      simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at ht
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one,
        Nat.cast_zero, sub_zero, one_mul]
      rw [hv] at ht
      apply (eq_sub_iff_add_eq).mpr
      simpa [add_comm] using ((sub_eq_iff_eq_add).mp ht).symm
    | succ k ih =>
      have hg : g ((h ^ (k + 1)) v) = (μ - 2 * (k + 1 : ℕ)) • ((h ^ (k + 1)) v) := by
        have hv' : ⁅-g, v⁆ = (-μ) • v := by simpa using congrArg Neg.neg hv
        have z := t.symm.lie_h_pow_toEnd_e hv' (k + 1)
        have z' : -(g ((h ^ (k + 1)) v)) =
            (-μ + 2 * (k + 1 : ℕ)) • ((h ^ (k + 1)) v) := by
          simpa [LieModule.toEnd_module_end] using z
        rw [neg_eq_iff_eq_neg, ← neg_smul] at z'
        convert z' using 1 <;> congr 1 <;> ring
      have ht := congrArg (fun f : Module.End ℚ V => f ((h ^ (k + 1)) v)) t.lie_e_f
      simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at ht
      rw [hg] at ht
      rw [pow_succ', Module.End.mul_apply, ih, map_sub, map_smul]
      rw [show h (r ((h ^ (k + 1)) v)) =
        r (h ((h ^ (k + 1)) v)) - (μ - 2 * (k + 1 : ℕ)) • ((h ^ (k + 1)) v) by
          apply (eq_sub_iff_add_eq).mpr
          simpa [add_comm] using ((sub_eq_iff_eq_add).mp ht).symm]
      simp only [← Module.End.mul_apply, ← pow_succ', Nat.cast_add, Nat.cast_one]
      module
  induction n with
  | zero =>
    intro v q k hv hk hn hz
    simpa using hn
  | succ n ih =>
    intro v q k hv hk hn hz
    have hrv : g (r v) = ((q + 2 : ℕ) : ℚ) • (r v) := by
      simpa [LieModule.toEnd_module_end] using t.lie_h_pow_toEnd_e hv 1
    have hrn : (r ^ n) (r v) = 0 := by
      simpa [pow_succ, Module.End.mul_apply] using hn
    have hnext : (h ^ (k + 1)) v = 0 := by
      rw [pow_succ', Module.End.mul_apply, hz, map_zero]
    have hrh : (h ^ (k + 1)) (r v) = 0 := by
      rw [lower_pow_raise t hv, hnext, hz]
      simp
    have hrzero : r v = 0 := ih (r v) (q + 2) (k + 1) hrv (by omega) hrn hrh
    by_contra hvzero
    have P : t.HasPrimitiveVectorWith v (q : ℚ) :=
      { ne_zero := hvzero, lie_h := hv, lie_e := hrzero }
    have hne := P.pow_toEnd_f_ne_zero_of_eq_nat rfl hk
    apply hne
    simpa [LieModule.toEnd_module_end] using hz

/-- Equation (A.4) for the rational K = 1 static sector. -/
theorem result : claim := by
  have wordSl2 (N : ℕ) (hN : 2 ≤ N) : IsSl2Triple ((LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w))) (Rbin N) (Hbin N) := by
    have localH_apply {N : ℕ} (a b : Fin N) (v : ((Fin N → Bool) → ℚ)) (w : (Fin N → Bool)) :
        localH a b v w = if w a = false ∧ w b = true then v (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) else 0 := rfl
    have weighted_swap {N : ℕ} (δ : Fin N → ℚ) (w : (Fin N → Bool))
        (a b : Fin N) (hab : a ≠ b) :
        (∑ i : Fin N, if ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w i then δ i else 0) -
          (∑ i : Fin N, if w i then δ i else 0) =
          (δ a - δ b) * ((if w b then 1 else 0) - (if w a then 1 else 0)) := by
      rw [← Finset.sum_sub_distrib]
      let f (i : Fin N) : ℚ :=
        (if ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w i then δ i else 0) - (if w i then δ i else 0)
      change ∑ i : Fin N, f i = _
      rw [← Finset.sum_erase_add Finset.univ f (a := a) (Finset.mem_univ a)]
      rw [← Finset.sum_erase_add (Finset.univ.erase a) f (a := b) (by simp [hab.symm])]
      have hz : ∑ i ∈ (Finset.univ.erase a).erase b, f i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hia : i ≠ a := by simpa using (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        have hib : i ≠ b := (Finset.mem_erase.mp hi).1
        simp [f, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hia hib]
      rw [hz, zero_add]
      cases hwa : w a <;> cases hwb : w b <;>
        simp [f, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, hwa, hwb] <;> ring
    have weight_swap_edge {N : ℕ} (p : Fin (N - 1)) (w : (Fin N → Bool))
        (hleft : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false) (hright : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true) :
        weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = weight w + 2 := by
      have hab : ((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) ≠ ((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) := by
        intro he
        have := congrArg Fin.val he
        dsimp only at this
        omega
      have he := weighted_swap (fun i : Fin N => (N : ℚ) - 1 - 2 * (i : ℕ)) w
        (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) hab
      change weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) - weight w =
        (((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) : Fin N) : ℕ)) -
          ((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) : Fin N) : ℕ))) *
          ((if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) then 1 else 0) - (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) then 1 else 0)) at he
      simp only [hleft, hright, Bool.false_eq_true, if_false, if_true, sub_zero, mul_one] at he
      have hc : (((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) : Fin N) : ℕ)) -
          ((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) : Fin N) : ℕ))) = 2 := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [hc] at he
      linarith
    have G_localH {N : ℕ} (p : Fin (N - 1)) :
        ⁅(LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w)), localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))⁆ =
          (-2 : ℚ) • localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) := by
      apply LinearMap.ext
      intro v
      funext w
      simp only [Ring.lie_def, LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, Pi.smul_apply, localH_apply]
      change weight w * (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true then
          v (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) else 0) -
        (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true then
          weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) *
            v (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) else 0) = _
      by_cases hw : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true
      · simp only [hw, and_self, if_true, smul_eq_mul]
        rw [weight_swap_edge p w hw.1 hw.2]
        ring
      · simp [localH_apply, hw]
    have G_H (N : ℕ) : ⁅(LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w)), Hbin N⁆ = (-2 : ℚ) • Hbin N := by
      unfold Hbin
      rw [lie_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact G_localH p
    have swapWord_involutive {N : ℕ} (a b : Fin N) (w : (Fin N → Bool)) :
        ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) = w := by
      ext i
      simp [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap]
    have G_localR {N : ℕ} (p : Fin (N - 1)) :
        ⁅(LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w)), localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))⁆ =
          (2 : ℚ) • localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) := by
      apply LinearMap.ext
      intro v
      funext w
      simp only [Ring.lie_def, LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, Pi.smul_apply, localR, localH_apply]
      change weight w * (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = true then
          v (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) else 0) -
        (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = true then
          weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) *
            v (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) else 0) = _
      by_cases hw : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = true
      · have hs : ((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w =
            ((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w := by simp [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_comm]
        have hl : ((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false := by
          simp [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, hw.1]
        have hr : ((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true := by
          simp [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, hw.2]
        have hg := weight_swap_edge p (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) hl hr
        rw [swapWord_involutive] at hg
        have he : weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = weight w - 2 := by
          rw [hs]
          linarith
        simp only [hw, and_self, if_true, smul_eq_mul]
        rw [he]
        ring
      · simp [hw]
    have G_R (N : ℕ) : ⁅(LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w)), Rbin N⁆ = (2 : ℚ) • Rbin N := by
      unfold Rbin
      rw [lie_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub (A := Module.End ℚ (((Fin N → Bool) → ℚ))) (((p : ℕ) + 1 : ℚ) * ((N : ℚ) - ((p : ℕ) + 1))),
        ← Ring.lie_def, G_localR, smul_comm]
    have local_commutator_apply {N : ℕ} (a b : Fin N)
        (v : ((Fin N → Bool) → ℚ)) (w : (Fin N → Bool)) :
        (localR a b * localH a b - localH a b * localR a b) v w =
          ((if w a then 1 else 0) - (if w b then 1 else 0) : ℚ) * v w := by
      simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, localR, localH_apply]
      simp only [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      have hii : (fun i => w (Equiv.swap a b (Equiv.swap b a i))) = w := by
        ext i
        simp [localH_apply, Equiv.swap_comm a b]
      have hii' : (fun i => w (Equiv.swap b a (Equiv.swap a b i))) = w := by
        ext i
        simp [localH_apply, Equiv.swap_comm a b]
      try simp only [hii, hii']
      cases hwa : w a <;> cases hwb : w b <;> simp [localH_apply, hwa, hwb, Function.comp_def, hii, hii']
    have localR_localH_commute {N : ℕ} (a b c d : Fin N)
        (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (hbd : b ≠ d) :
        localR a b * localH c d = localH c d * localR a b := by
      have localH_apply {N : ℕ} (a b : Fin N) (v : ((Fin N → Bool) → ℚ)) (w : (Fin N → Bool)) :
          localH a b v w = if w a = false ∧ w b = true then v (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) else 0 := rfl
      apply LinearMap.ext
      intro v
      funext w
      by_cases had : a = d
      · subst d
        cases hwa : w a <;> cases hwb : w b <;> cases hwc : w c <;>
          simp [localH_apply, Module.End.mul_apply, localR, localH_apply, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Function.comp_apply,
            Equiv.swap_apply_def, hab, hab.symm, hac, hac.symm, hbd, hbd.symm, hwa, hwb, hwc]
      · by_cases hbc : b = c
        · subst c
          cases hwa : w a <;> cases hwb : w b <;> cases hwd : w d <;>
            simp [localH_apply, Module.End.mul_apply, localR, localH_apply, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Function.comp_apply,
              Equiv.swap_apply_def, hab, hab.symm, hac, hac.symm, hbd, hbd.symm, hwa, hwb, hwd]
        · have hs : ((Equiv.swap c d).arrowCongr (Equiv.refl Bool)) (((Equiv.swap b a).arrowCongr (Equiv.refl Bool)) w) = ((Equiv.swap b a).arrowCongr (Equiv.refl Bool)) (((Equiv.swap c d).arrowCongr (Equiv.refl Bool)) w) := by
            ext i
            simp only [Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Function.comp_apply, Equiv.swap_apply_def]
            by_cases hib : i = b
            · subst i
              simp [Equiv.swap_apply_def, hab, hab.symm, hcd, hcd.symm,
                hac, hac.symm, hbd, hbd.symm, had, (Ne.symm had), hbc, (Ne.symm hbc)]
            · by_cases hia : i = a
              · subst i
                simp [Equiv.swap_apply_def, hab, hab.symm, hcd, hcd.symm,
                  hac, hac.symm, hbd, hbd.symm, had, (Ne.symm had), hbc, (Ne.symm hbc)]
              · by_cases hic : i = c
                · subst i
                  simp [Equiv.swap_apply_def, hab, hab.symm, hcd, hcd.symm,
                    hac, hac.symm, hbd, hbd.symm, had, (Ne.symm had), hbc, (Ne.symm hbc)]
                · by_cases hid : i = d
                  · subst i
                    simp [Equiv.swap_apply_def, hab, hab.symm, hcd, hcd.symm,
                      hac, hac.symm, hbd, hbd.symm, had, (Ne.symm had), hbc, (Ne.symm hbc)]
                  · simp [Equiv.swap_apply_def, hib, hia, hic, hid]
          simp only [Module.End.mul_apply, localR, localH_apply]
          have hca : ((Equiv.swap b a).arrowCongr (Equiv.refl Bool)) w c = w c := by
            simp [localH_apply, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_def, hac.symm, (Ne.symm hbc)]
          have hda : ((Equiv.swap b a).arrowCongr (Equiv.refl Bool)) w d = w d := by
            simp [localH_apply, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_def, (Ne.symm had), hbd.symm]
          have hbc' : ((Equiv.swap c d).arrowCongr (Equiv.refl Bool)) w b = w b := by
            simp [localH_apply, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_def, hbc, hbd]
          have hac' : ((Equiv.swap c d).arrowCongr (Equiv.refl Bool)) w a = w a := by
            simp [localH_apply, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_def, hac, had]
          simp only [hca, hda, hbc', hac']
          split_ifs <;> simp only [hs]
    have R_H (N : ℕ) : ⁅Rbin N, Hbin N⁆ = (LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w)) := by
      have ho (p q : Fin (N - 1)) (hpq : p ≠ q) :
          ⁅localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)), localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) q)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) q))⁆ = 0 := by
        rw [Ring.lie_def, sub_eq_zero]
        apply localR_localH_commute
        · intro he; have := congrArg Fin.val he; simp [localH_apply, ] at this
        · intro he; have := congrArg Fin.val he; simp [localH_apply, ] at this
        · intro he; apply hpq; apply Fin.ext
          have hv := congrArg (Fin.val : Fin N → ℕ) he
          exact hv
        · intro he; apply hpq; apply Fin.ext
          have hv := congrArg Fin.val he
          dsimp only at hv
          omega
      have he : ⁅Rbin N, Hbin N⁆ =
          ∑ p : Fin (N - 1), (((p : ℕ) + 1 : ℚ) * ((N : ℚ) - ((p : ℕ) + 1))) •
            ⁅localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)), localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))⁆ := by
        unfold Rbin Hbin
        rw [sum_lie]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm,
          ← smul_sub (A := Module.End ℚ (((Fin N → Bool) → ℚ)))
            (((p : ℕ) + 1 : ℚ) * ((N : ℚ) - ((p : ℕ) + 1)))]
        apply congrArg (fun z : Module.End ℚ (((Fin N → Bool) → ℚ)) =>
          (((p : ℕ) + 1 : ℚ) * ((N : ℚ) - ((p : ℕ) + 1))) • z)
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        change (∑ q : Fin (N - 1),
          ⁅localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)), localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) q)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) q))⁆) = _
        rw [Finset.sum_eq_single p]
        · intro q hq hqp
          rw [ho p q (Ne.symm hqp)]
        · simp
      rw [he]
      apply LinearMap.ext
      intro v
      funext w
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
        Pi.smul_apply, smul_eq_mul, Ring.lie_def]
      change (∑ p : Fin (N - 1), (((p : ℕ) + 1 : ℚ) * ((N : ℚ) - ((p : ℕ) + 1))) *
        (localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) * localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) -
          localH (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) * localR (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))) v w) =
        weight w * v w
      have hd (p : Fin (N - 1)) := local_commutator_apply (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) v w
      simp_rw [hd]
      simp only [← mul_assoc, ← Finset.sum_mul]
      congr 1
      let x (i : ℕ) : ℚ := if hi : i < N then if w ⟨i, hi⟩ then 1 else 0 else 0
      have positional_telescope (N : ℕ) (x : ℕ → ℚ) :
          (∑ p ∈ Finset.range (N - 1), ((p + 1 : ℕ) : ℚ) * ((N : ℚ) - (p + 1)) *
            (x p - x (p + 1))) =
          ∑ i ∈ Finset.range N, ((N : ℚ) - 1 - 2 * i) * x i := by
        cases N with
        | zero => simp
        | succ N =>
          simp only [Nat.add_sub_cancel]
          have he :
              (∑ p ∈ Finset.range N, ((p + 1 : ℕ) : ℚ) *
                ((N + 1 : ℕ) - (p + 1 : ℕ) : ℚ) * (x p - x (p + 1))) =
              (∑ p ∈ Finset.range N, ((N + 1 : ℕ) - 1 - 2 * (p : ℚ)) * x p) +
              ∑ p ∈ Finset.range N, ((p : ℚ) * ((N + 1 : ℕ) - p : ℚ) * x p -
                ((p + 1 : ℕ) : ℚ) * ((N + 1 : ℕ) - (p + 1 : ℕ) : ℚ) * x (p + 1)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            push_cast
            ring
          have ht := Finset.sum_range_sub'
            (fun p : ℕ => (p : ℚ) * ((N + 1 : ℕ) - p : ℚ) * x p) N
          simp only [Nat.cast_add, Nat.cast_one] at he ht ⊢
          rw [he, ht, Finset.sum_range_succ]
          push_cast
          ring
      have ht := positional_telescope N x
      rw [Finset.sum_fin_eq_sum_range]
      unfold weight
      rw [Finset.sum_fin_eq_sum_range]
      convert ht using 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hi0 : i < N := by omega
        have hi1 : i + 1 < N := by omega
        simp [localH_apply, x, hi', hi0, hi1, ]
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        cases hw : w ⟨i, hi'⟩ <;> simp [localH_apply, x, hi', hw]
    have Gbin_ne_zero (N : ℕ) (hN : 2 ≤ N) : (LinearMap.mulLeft ℚ (fun w : Fin N → Bool => weight w)) ≠ 0 := by
      intro hz
      let a : Fin N := ⟨0, by omega⟩
      let w : (Fin N → Bool) := fun i => if i = a then true else false
      have hw : weight w = (N : ℚ) - 1 := by
        unfold weight
        rw [Finset.sum_eq_single a]
        · simp [w, a]
        · intro i hi hia
          simp [w, hia]
        · simp
      have he := congrFun (congrArg (fun f : Module.End ℚ (((Fin N → Bool) → ℚ)) => f (fun _ => 1)) hz) w
      change weight w * 1 = 0 at he
      rw [hw] at he
      have hNq : (2 : ℚ) ≤ N := by exact_mod_cast hN
      linarith
    exact {
      h_ne_zero := Gbin_ne_zero N hN
      lie_e_f := R_H N
      lie_h_e_nsmul := by simpa [two_smul] using G_R N
      lie_h_f_nsmul := by
        have z := G_H N
        rw [show (-2 : ℚ) = -(2 : ℚ) by rfl, neg_smul (M := Module.End ℚ (((Fin N → Bool) → ℚ))), two_smul] at z
        simpa only [two_smul] using z
    }
  have mem_W_iff (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) :
      v ∈ W L M S ↔ ∀ w, v w ≠ 0 → ones w = M - 1 ∧ level w = S := by
    rw [W, (Pi.basisFun ℚ ((Fin (L - 1) → Bool))).mem_span_image]
    simp [Set.subset_def, sector, Finsupp.mem_support_iff]
  have W_weight (L M S : ℕ) (hM : 1 ≤ M) (hML : M ≤ L)
      (v : ((Fin (L - 1) → Bool) → ℚ)) (hv : v ∈ W L M S) :
      (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) v = (2 * (S : ℚ) - ((M - 1) * (L - M) : ℕ)) • v := by
    rw [mem_W_iff] at hv
    funext w
    change weight w * v w = _
    by_cases hw : v w = 0
    · simp [hw]
    · have he := hv w hw
      rw [weight_eq_level, he.1, he.2]
      simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      congr 1
      have hn : (L - 1) = (M - 1) + (L - M) := by omega
      rw [hn, Nat.cast_add]
      ring
  have raising_eventually_zero {V : Type} [AddCommGroup V] [Module ℚ V]
      {g r h : Module.End ℚ V} [FiniteDimensional ℚ V]
      (t : IsSl2Triple g r h) {v : V} {μ : ℚ} (hv : g v = μ • v) :
      ∃ n : ℕ, (r ^ n) v = 0 := by
    classical
    by_contra! contra
    let ev (n : ℕ) : ℚ := μ + 2 * n
    have hi : Function.Injective ev := by
      intro n m hnm
      dsimp [ev] at hnm
      exact Nat.cast_injective (by linarith : (n : ℚ) = m)
    have aux (ν : Set.range ev) : g.HasEigenvector ν ((r ^ ν.property.choose) v) := by
      refine ⟨?_, contra _⟩
      set n := ν.property.choose
      have he : ev n = (ν : ℚ) := ν.property.choose_spec
      rw [Module.End.mem_eigenspace_iff]
      calc
        g ((r ^ n) v) = ev n • ((r ^ n) v) := by
          simpa [LieModule.toEnd_module_end, ev] using t.lie_h_pow_toEnd_e hv n
        _ = (ν : ℚ) • ((r ^ n) v) := by rw [he]
    have hf := (g.eigenvectors_linearIndependent (Set.range ev) _ aux).finite
    exact (Set.infinite_range_of_injective hi) (Set.toFinite _)
  have lowering_kernel_zero {V : Type} [AddCommGroup V] [Module ℚ V]
      {g r h : Module.End ℚ V} [FiniteDimensional ℚ V]
      (t : IsSl2Triple g r h) {v : V} {q k : ℕ}
      (hv : g v = (q : ℚ) • v) (hk : k ≤ q) (hz : (h ^ k) v = 0) : v = 0 := by
    obtain ⟨n, hn⟩ := raising_eventually_zero t hv
    exact lowering_kernel_zero_aux t n v q k hv hk hn hz
  have restrict_injective (L M S k : ℕ) (hM : 1 ≤ M) (hML : M ≤ L)
      (hN : 2 ≤ L - 1) (hμ : (M - 1) * (L - M) + k ≤ 2 * S) :
      Function.Injective (restrict L M S k) := by
    let q := 2 * S - (M - 1) * (L - M)
    have hq : k ≤ q := by dsimp [q]; omega
    have hqeq : (q : ℚ) = 2 * (S : ℚ) - ((M - 1) * (L - M) : ℕ) := by
      dsimp [q]
      rw [Nat.cast_sub (by omega), Nat.cast_mul]
      norm_num
    intro v u he
    apply Subtype.ext
    have hw : (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) ((v - u : W L M S) : ((Fin (L - 1) → Bool) → ℚ)) =
        (q : ℚ) • ((v - u : W L M S) : ((Fin (L - 1) → Bool) → ℚ)) := by
      rw [hqeq]
      exact W_weight L M S hM hML _ (v - u).property
    have hz : (H L M ^ k) ((v - u : W L M S) : ((Fin (L - 1) → Bool) → ℚ)) = 0 := by
      have he' := congrArg (fun z : W L M (S - k) => (z : ((Fin (L - 1) → Bool) → ℚ))) he
      change (H L M ^ k) (v : ((Fin (L - 1) → Bool) → ℚ)) = (H L M ^ k) (u : ((Fin (L - 1) → Bool) → ℚ)) at he'
      change (H L M ^ k) ((v : ((Fin (L - 1) → Bool) → ℚ)) - (u : ((Fin (L - 1) → Bool) → ℚ))) = 0
      rw [map_sub, he', sub_self]
    have hz' := lowering_kernel_zero (wordSl2 (L - 1) hN) hw hq hz
    exact sub_eq_zero.mp hz'
  have projectW_apply (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) (w : (Fin (L - 1) → Bool)) :
      (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v w = if ones w = M - 1 ∧ level w = S then v w else 0 := by
    simp only [LinearMap.mulLeft_apply, Pi.mul_apply, ite_mul, one_mul, zero_mul]
  have projectW_mem (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) : (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v ∈ W L M S := by
    rw [mem_W_iff]
    intro w hw
    by_contra hn
    apply hw
    simp [projectW_apply, hn]
  have projectW_self (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) (hv : v ∈ W L M S) :
      (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v = v := by
    rw [mem_W_iff] at hv
    funext w
    by_cases hw : v w = 0
    · simp [projectW_apply, hw]
    · simp [projectW_apply, hv w hw]
  have localH_apply {N : ℕ} (a b : Fin N) (v : ((Fin N → Bool) → ℚ)) (w : (Fin N → Bool)) :
      localH a b v w = if w a = false ∧ w b = true then v (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) else 0 := rfl
  have twos_swap {N : ℕ} (a b : Fin N) (w : (Fin N → Bool)) :
      ones (((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w) = ones w := by
    simp only [ones, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap]
    exact Equiv.sum_comp (Equiv.swap a b) (fun i => if w i then 1 else 0)
  have weighted_swap {N : ℕ} (δ : Fin N → ℚ) (w : (Fin N → Bool))
      (a b : Fin N) (hab : a ≠ b) :
      (∑ i : Fin N, if ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w i then δ i else 0) -
        (∑ i : Fin N, if w i then δ i else 0) =
        (δ a - δ b) * ((if w b then 1 else 0) - (if w a then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib]
    let f (i : Fin N) : ℚ :=
      (if ((Equiv.swap a b).arrowCongr (Equiv.refl Bool)) w i then δ i else 0) - (if w i then δ i else 0)
    change ∑ i : Fin N, f i = _
    rw [← Finset.sum_erase_add Finset.univ f (a := a) (Finset.mem_univ a)]
    rw [← Finset.sum_erase_add (Finset.univ.erase a) f (a := b) (by simp [hab.symm])]
    have hz : ∑ i ∈ (Finset.univ.erase a).erase b, f i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hia : i ≠ a := by simpa using (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hib : i ≠ b := (Finset.mem_erase.mp hi).1
      simp [f, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hia hib]
    rw [hz, zero_add]
    cases hwa : w a <;> cases hwb : w b <;>
      simp [f, Equiv.arrowCongr, Equiv.refl, Equiv.coe_fn_mk, Equiv.symm_swap, hwa, hwb] <;> ring
  have weight_swap_edge {N : ℕ} (p : Fin (N - 1)) (w : (Fin N → Bool))
      (hleft : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false) (hright : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true) :
      weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = weight w + 2 := by
    have hab : ((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) ≠ ((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) := by
      intro he
      have := congrArg Fin.val he
      dsimp only at this
      omega
    have he := weighted_swap (fun i : Fin N => (N : ℚ) - 1 - 2 * (i : ℕ)) w
      (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) hab
    change weight (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) - weight w =
      (((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) : Fin N) : ℕ)) -
        ((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) : Fin N) : ℕ))) *
        ((if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) then 1 else 0) - (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) then 1 else 0)) at he
    simp only [hleft, hright, Bool.false_eq_true, if_false, if_true, sub_zero, mul_one] at he
    have hc : (((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p) : Fin N) : ℕ)) -
        ((N : ℚ) - 1 - 2 * ((((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p) : Fin N) : ℕ))) = 2 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hc] at he
    linarith
  have level_swap_edge {N : ℕ} (p : Fin (N - 1)) (w : (Fin N → Bool))
      (hleft : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false) (hright : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true) :
      level (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = level w + 1 := by
    have hw := weight_swap_edge p w hleft hright
    have ht := twos_swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) w
    rw [weight_eq_level, weight_eq_level, ht] at hw
    have he : (level (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) : ℚ) = (level w : ℚ) + 1 := by
      linarith
    exact_mod_cast he
  have H_projectW (L M S : ℕ) (hS : 1 ≤ S) (v : ((Fin (L - 1) → Bool) → ℚ)) :
      H L M ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v) = (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = (S - 1) then 1 else 0)) (H L M v) := by
    funext w
    simp only [H, Hbin, LinearMap.sum_apply, Finset.sum_apply, localH_apply, projectW_apply]
    have he : (if ones w = M - 1 ∧ level w = S - 1 then
        ∑ p : Fin ((L - 1) - 1), if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true then
          v (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) else 0
        else 0) = ∑ p : Fin ((L - 1) - 1),
          if ones w = M - 1 ∧ level w = S - 1 then
            (if w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true then
              v (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) else 0) else 0 := by
      by_cases hp : ones w = M - 1 ∧ level w = S - 1 <;> simp [projectW_apply, hp]
    rw [he]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hc : w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) = false ∧ w (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) = true
    · have ht := twos_swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p)) w
      have hs := level_swap_edge p w hc.1 hc.2
      have he : (ones (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = M - 1 ∧
          level (((Equiv.swap (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨i, by omega⟩ : Fin N)) p)) (((fun {N : ℕ} (i : Fin (N - 1)) => (⟨(i : ℕ) + 1, by omega⟩ : Fin N)) p))).arrowCongr (Equiv.refl Bool)) w) = S) ↔
          (ones w = M - 1 ∧ level w = S - 1) := by rw [ht, hs]; omega
      simp only [hc, and_self, if_true]
      simp only [he]
    · simp [projectW_apply, hc]
  have H_pow_projectW (L M S k : ℕ) (hk : k ≤ S) (v : ((Fin (L - 1) → Bool) → ℚ)) :
      (H L M ^ k) ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v) = (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = (S - k) then 1 else 0)) ((H L M ^ k) v) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih (by omega)]
      rw [H_projectW L M (S - k) (by omega)]
      have he : (S - k) - 1 = S - (k + 1) := by omega
      rw [he]
      rfl
  have G_projectW (L M S : ℕ) (v : ((Fin (L - 1) → Bool) → ℚ)) :
      (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) v) = (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = S then 1 else 0)) ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) v) := by
    funext w
    simp only [projectW_apply, LinearMap.mulLeft_apply, Pi.mul_apply, ite_mul, one_mul, zero_mul]
    change weight w * (if ones w = M - 1 ∧ level w = S then v w else 0) =
      (if ones w = M - 1 ∧ level w = S then weight w * v w else 0)
    split_ifs <;> simp
  have sl2Dual {V : Type} [AddCommGroup V] [Module ℚ V]
      {g r h : Module.End ℚ V} (t : IsSl2Triple g r h) :
      IsSl2Triple (-g.dualMap) (-r.dualMap) (-h.dualMap) := by
    exact {
      h_ne_zero := by
        intro hz
        apply t.h_ne_zero
        apply LinearMap.ext
        intro v
        apply (Module.forall_dual_apply_eq_zero_iff ℚ (g v)).mp
        intro φ
        have he := congrArg (fun f : Module.End ℚ (Module.Dual ℚ V) => f φ v) hz
        simpa [LinearMap.dualMap_apply] using he
      lie_e_f := by
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro v
        have he := congrArg (fun f : Module.End ℚ V => φ (f v)) t.lie_e_f
        simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub] at he
        simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
          LinearMap.dualMap_apply, map_neg]
        linarith
      lie_h_e_nsmul := by
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro v
        have he := congrArg (fun f : Module.End ℚ V => φ (f v)) t.lie_h_e_nsmul
        simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub,
          two_smul, LinearMap.add_apply, map_add] at he
        simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
          LinearMap.dualMap_apply, map_neg, two_smul, LinearMap.add_apply]
        linarith
      lie_h_f_nsmul := by
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro v
        have he := congrArg (fun f : Module.End ℚ V => φ (f v)) t.lie_h_f_nsmul
        simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub,
          two_smul, LinearMap.add_apply, map_add, LinearMap.neg_apply, map_neg] at he
        simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
          LinearMap.dualMap_apply, map_neg, two_smul, LinearMap.add_apply]
        linarith
    }
  have neg_dual_pow_apply {V : Type} [AddCommGroup V] [Module ℚ V] (f : Module.End ℚ V) (k : ℕ) (φ : Module.Dual ℚ V) (v : V) :
      ((-f.dualMap) ^ k) φ v = (-1 : ℚ) ^ k * φ ((f ^ k) v) := by
    induction k generalizing v with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, LinearMap.dualMap_apply]
      rw [ih]
      have hp : (f ^ k) (f v) = f ((f ^ k) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']
      rw [hp]
      ring
  have restrict_surjective (L M S k : ℕ) (hM : 1 ≤ M) (hML : M ≤ L)
      (hN : 2 ≤ L - 1) (hk : k ≤ S) (hμ : 2 * S ≤ (M - 1) * (L - M) + k) :
      Function.Surjective (restrict L M S k) := by
    apply LinearMap.dualMap_injective_iff.mp
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro φ hφ
    let ψ : Module.Dual ℚ (((Fin (L - 1) → Bool) → ℚ)) := φ.comp (projectToW L M (S - k))
    let q := (M - 1) * (L - M) - 2 * (S - k)
    have hq : k ≤ q := by dsimp [projectW_apply, q]; omega
    have hqeq : (q : ℚ) = -(2 * ((S - k : ℕ) : ℚ) - ((M - 1) * (L - M) : ℕ)) := by
      dsimp [projectW_apply, q]
      rw [Nat.cast_sub (by omega), Nat.cast_mul]
      norm_num
    have hψweight : (- ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w))).dualMap) ψ = (q : ℚ) • ψ := by
      apply LinearMap.ext
      intro v
      have he : projectToW L M (S - k) ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) v) =
          (2 * ((S - k : ℕ) : ℚ) - ((M - 1) * (L - M) : ℕ)) • projectToW L M (S - k) v := by
        apply Subtype.ext
        change (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = (S - k) then 1 else 0)) ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) v) =
          (2 * ((S - k : ℕ) : ℚ) - ((M - 1) * (L - M) : ℕ)) • (LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => if ones w = M - 1 ∧ level w = (S - k) then 1 else 0)) v
        rw [← G_projectW]
        exact W_weight L M (S - k) hM hML _ (projectW_mem L M (S - k) v)
      simp only [LinearMap.neg_apply, LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul]
      change -(φ (projectToW L M (S - k) ((LinearMap.mulLeft ℚ (fun w : Fin (L - 1) → Bool => weight w)) v))) = _
      rw [he, map_smul, hqeq]
      simp [projectW_apply, ψ, smul_eq_mul]
      ring
    have hψzero : ((- (H L M).dualMap) ^ k) ψ = 0 := by
      apply LinearMap.ext
      intro v
      rw [neg_dual_pow_apply]
      have he := congrArg (fun f : Module.Dual ℚ (W L M S) => f (projectToW L M S v)) hφ
      change φ (restrict L M S k (projectToW L M S v)) = 0 at he
      have heq : projectToW L M (S - k) ((H L M ^ k) v) =
          restrict L M S k (projectToW L M S v) := by
        apply Subtype.ext
        exact (H_pow_projectW L M S k hk v).symm
      change (-1 : ℚ) ^ k * φ (projectToW L M (S - k) ((H L M ^ k) v)) = 0
      rw [heq, he, mul_zero]
    have hψ := lowering_kernel_zero (sl2Dual (wordSl2 (L - 1) hN)) hψweight hq hψzero
    apply LinearMap.ext
    intro y
    have he := congrArg (fun f : Module.Dual ℚ (((Fin (L - 1) → Bool) → ℚ)) => f (y : ((Fin (L - 1) → Bool) → ℚ))) hψ
    change φ (projectToW L M (S - k) (y : ((Fin (L - 1) → Bool) → ℚ))) = 0 at he
    have heq : projectToW L M (S - k) (y : ((Fin (L - 1) → Bool) → ℚ)) = y := by
      apply Subtype.ext
      exact projectW_self L M (S - k) _ y.property
    rwa [heq] at he
  have level_small_bin {N : ℕ} (hN : N ≤ 1) (w : (Fin N → Bool)) : level w = 0 := by
    unfold level
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hn : ¬i < j := by
      have hi' := i.isLt
      have hj' := j.isLt
      change ¬i.val < j.val
      omega
    simp [hn]
  have W_small_bin (L M S : ℕ) (hN : L - 1 ≤ 1) (hS : 0 < S) : W L M S = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    funext w
    by_contra hw
    have he := (mem_W_iff L M S v).mp hv w hw
    have hl := level_small_bin hN w
    omega
  intro L M hM hML S k hk
  by_cases hN : 2 ≤ L - 1
  · by_cases hμ : (M - 1) * (L - M) + k ≤ 2 * S
    · have hi := restrict_injective L M S k hM hML hN hμ
      have hr := LinearMap.finrank_range_of_inj hi
      have hd := LinearMap.finrank_le_finrank_of_injective hi
      rw [hr, min_eq_left hd]
    · have hs := restrict_surjective L M S k hM hML hN hk (by omega)
      have hr : Module.finrank ℚ (LinearMap.range (restrict L M S k)) =
          Module.finrank ℚ (W L M (S - k)) := by
        rw [LinearMap.range_eq_top.mpr hs, finrank_top]
      have hd := LinearMap.finrank_le_finrank_of_surjective hs
      rw [hr, min_eq_right hd]
  · by_cases hS : S = 0
    · have hk0 : k = 0 := by omega
      subst S
      subst k
      have hi : Function.Injective (restrict L M 0 0) := by
        intro v u he
        apply Subtype.ext
        exact congrArg (fun z : W L M (0 - 0) => (z : ((Fin (L - 1) → Bool) → ℚ))) he
      rw [LinearMap.finrank_range_of_inj hi]
      simp
    · have hd : Module.finrank ℚ (W L M S) = 0 := by
        rw [W_small_bin L M S (by omega) (by omega)]
        simp
      have hr := (restrict L M S k).finrank_range_le
      rw [hd] at hr ⊢
      simp [Nat.eq_zero_of_le_zero hr]

end D5.S3.Quantum.SpinChains.HypereclecticNonShortening
