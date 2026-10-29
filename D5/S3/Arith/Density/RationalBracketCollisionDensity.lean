/- GID: D5/S3/Arith/Density/RationalBracketCollisionDensity
   generality: S
   mirror-B: D5/B/S3/Arith/Density/RationalBracketCollisionDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Rat.Floor, mathlib/module/Mathlib.Data.Nat.Periodic]
   utility: none
   digest: Every finite rational-modulus bracket expression has an existing rational collision density, with arbitrary integer coefficients and distinct nonnegative image values. -/

import D5.S3.ObserverMemory.Prediction.EventualCycleAverage
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Periodic

open Filter Finset
open scoped Topology BigOperators Classical
namespace D5.S3.Arith.Density.RationalBracketCollisionDensity
noncomputable section

private theorem affine_blocks (w : ℕ → ℤ) (q : ℕ) (d : ℤ)
    (h : ∀ n, w (n + q) = w n + d) (r s : ℕ) :
    w (r + s * q) = w r + (s : ℤ) * d := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]
    push_cast
    ring

private theorem affine_image_tail (w : ℕ → ℤ) (q : ℕ) (hq : 0 < q) (d : ℤ)
    (h : ∀ n, w (n + q) = w n + d) :
    ∃ M p : ℕ, 0 < p ∧ ∀ x : ℕ, M ≤ x →
      ((∃ n, w n = (x + p : ℕ)) ↔ ∃ n, w n = (x : ℤ)) := by
  let M := (∑ r : Fin q, (w r).natAbs) + 1
  have hb (r : Fin q) : w r < (M : ℤ) := by
    have hr : (w r).natAbs ≤ ∑ j : Fin q, (w j).natAbs :=
      Finset.single_le_sum (f := fun j : Fin q => (w j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    have hr' : ((w r).natAbs : ℤ) < (M : ℤ) := by exact_mod_cast (show (w r).natAbs < M by omega)
    exact lt_of_le_of_lt (Int.le_natAbs) hr'
  have decomp (n : ℕ) : w n = w (n % q) + ((n / q : ℕ) : ℤ) * d := by
    have hh := affine_blocks w q d h (n % q) (n / q)
    rw [Nat.mul_comm (n / q) q] at hh
    simpa only [Nat.mod_add_div] using hh
  by_cases hd : d ≤ 0
  · refine ⟨M, 1, by omega, ?_⟩
    have hnot (x : ℕ) (hx : M ≤ x) : ¬ ∃ n, w n = (x : ℤ) := by
      rintro ⟨n, hn⟩
      have hr := hb ⟨n % q, Nat.mod_lt n hq⟩
      have hm : ((n / q : ℕ) : ℤ) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hd
      rw [decomp n] at hn
      have hx' : (M : ℤ) ≤ x := by exact_mod_cast hx
      dsimp at hr
      linarith
    intro x hx
    exact iff_of_false (hnot (x + 1) (by omega)) (hnot x hx)
  · have hd : 0 < d := by omega
    let p := d.toNat
    have hp : 0 < p := by dsimp [p]; omega
    have hpz : (p : ℤ) = d := Int.toNat_of_nonneg (by omega)
    refine ⟨M, p, hp, ?_⟩
    intro x hx
    constructor
    · rintro ⟨n, hn⟩
      let r := n % q
      let s := n / q
      have hs : 0 < s := by
        by_contra hs
        have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
        have hr := hb ⟨r, Nat.mod_lt n hq⟩
        have hn' := decomp n
        change w n = w r + (s : ℤ) * d at hn'
        rw [hs0] at hn'
        simp only [Nat.cast_zero, zero_mul, add_zero] at hn'
        have hx' : (M : ℤ) ≤ x := by exact_mod_cast hx
        push_cast at hn
        rw [hpz] at hn
        dsimp at hr
        linarith
      refine ⟨r + (s - 1) * q, ?_⟩
      rw [affine_blocks w q d h]
      have hn' := decomp n
      change w n = w r + (s : ℤ) * d at hn'
      have hs' : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by omega
      rw [hs']
      push_cast at hn
      rw [hpz] at hn
      nlinarith
    · rintro ⟨n, hn⟩
      refine ⟨n + q, ?_⟩
      rw [h, hn]
      push_cast
      rw [hpz]

private theorem eventual_periodic_density (P : ℕ → Prop)
    (M p : ℕ) (hp : 0 < p)
    (hP : ∀ x, M ≤ x → (P (x + p) ↔ P x)) :
    ∃ a : ℚ, Tendsto
      (fun N : ℕ => (((Finset.range (N + 1)).filter P).card : ℝ) / (N : ℝ))
      atTop (𝓝 (a : ℝ)) := by
  classical
  let update : (ℕ → Prop) → (ℕ → Prop) := fun f n => f (n + 1)
  let cycle : Fin p → (ℕ → Prop) := fun j n => P (M + (j.val + n) % p)
  let value : (ℕ → Prop) → ℝ := fun f => if f 0 then 1 else 0
  have htail : Function.Periodic (fun n => P (M + n)) p := by
    intro n
    apply propext
    simpa [Nat.add_assoc] using hP (M + n) (by omega)
  have hm (n : ℕ) : P (M + n % p) = P (M + n) := htail.map_mod_nat n
  have hi (t : ℕ) : (update^[t]) P = fun n => P (t + n) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      funext n
      dsimp [update]
      congr 1
      omega
  have hc (t : ℕ) : (update^[M + t]) P = cycle ⟨t % p, Nat.mod_lt t hp⟩ := by
    rw [hi]
    funext n
    dsimp [cycle]
    rw [Nat.add_assoc, ← hm (t + n)]
    simp [Nat.add_mod]
  have havg := D5.S3.ObserverMemory.Prediction.EventualCycleAverage.eventual_cycle_average
    update value P hp cycle M hc
  let a : ℚ := (∑ j : Fin p, if P (M + j.val) then (1 : ℚ) else 0) / (p : ℚ)
  have ha : (a : ℝ) = (∑ j : Fin p, value (cycle j)) / (p : ℝ) := by
    simp [a, value, cycle, Nat.mod_eq_of_lt]
  have hs (N : ℕ) :
      (((Finset.range N).filter P).card : ℝ) = ∑ t ∈ Finset.range N, value ((update^[t]) P) := by
    simp [hi, value]
  have hlim : Tendsto
      (fun N : ℕ => (((Finset.range N).filter P).card : ℝ) / (N : ℝ))
      atTop (𝓝 (a : ℝ)) := by
    simpa only [← hs, ← ha] using havg
  have hshift : Tendsto
      (fun N : ℕ => (((Finset.range (N + 1)).filter P).card : ℝ) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 (a : ℝ)) := by
    exact (hlim.comp ((tendsto_add_atTop_iff_nat 1).mpr tendsto_id)).congr'
      (Eventually.of_forall fun N => rfl)
  have hratio : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    have htotal : Tendsto (fun N : ℕ => 1 + (1 : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hh
    apply htotal.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  refine ⟨a, ?_⟩
  have heq : (fun N : ℕ =>
        ((((Finset.range (N + 1)).filter P).card : ℝ) / ((N + 1 : ℕ) : ℝ)) *
          (((N + 1 : ℕ) : ℝ) / (N : ℝ))) =
      (fun N : ℕ => (((Finset.range (N + 1)).filter P).card : ℝ) / (N : ℝ)) := by
    funext N
    have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [heq, mul_one] using hshift.mul hratio

/-- The integer sequence specified by a finite rational-modulus bracket expression. -/
def bracket {t : ℕ} (c : Fin t → ℤ) (α : Fin t → ℚ) (n : ℕ) : ℤ :=
  ∑ i, c i * ⌊(n : ℚ) * α i⌋

private theorem bracket_affine {t : ℕ} (c : Fin t → ℤ) (α : Fin t → ℚ) :
    ∃ q : ℕ, 0 < q ∧ ∃ d : ℤ, ∀ n, bracket c α (n + q) = bracket c α n + d := by
  have aux (s : Finset (Fin t)) : ∃ q : ℕ, 0 < q ∧ ∃ d : ℤ,
      ∀ n, (∑ i ∈ s, c i * ⌊((n + q : ℕ) : ℚ) * α i⌋) =
        (∑ i ∈ s, c i * ⌊(n : ℚ) * α i⌋) + d := by
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by omega, 0, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨q, hq, d, hd⟩ := ih
      let r := (α i).den
      have hr : 0 < r := Rat.den_pos _
      have hα : (r : ℚ) * α i = ((α i).num : ℚ) := by
        calc
          (r : ℚ) * α i = (r : ℚ) * ((α i).num / (α i).den) :=
            congrArg (fun a : ℚ => (r : ℚ) * a) (Rat.num_div_den _).symm
          _ = _ := by dsimp [r]; field_simp
      have hi' (n : ℕ) : c i * ⌊((n + r : ℕ) : ℚ) * α i⌋ =
          c i * ⌊(n : ℚ) * α i⌋ + c i * (α i).num := by
        rw [Nat.cast_add, add_mul, hα, Int.floor_add_intCast]
        ring
      refine ⟨q * r, Nat.mul_pos hq hr, (q : ℤ) * (c i * (α i).num) + (r : ℤ) * d, ?_⟩
      intro n
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have h1 := affine_blocks (fun n => c i * ⌊(n : ℚ) * α i⌋) r
        (c i * (α i).num) hi' n q
      have h2 := affine_blocks (fun n => ∑ i ∈ s, c i * ⌊(n : ℚ) * α i⌋) q d hd n r
      simp only [Nat.mul_comm r q] at h2
      rw [h1, h2]
      ring
  simpa only [bracket] using aux Finset.univ

/-- Membership in the actual image, so repeated indices count only once. -/
def collision {t : ℕ} (c : Fin t → ℤ) (α : Fin t → ℚ) (k x : ℕ) : Prop :=
  (∃ n : ℕ, bracket c α n = (x : ℤ)) ∧
    (∃ n : ℕ, bracket c α n = ((x + k : ℕ) : ℤ))

/-- The exact rationality subquestion, with inclusive interval and denominator N. -/
def claim : Prop :=
  ∀ (t : ℕ) (c : Fin t → ℤ) (α : Fin t → ℚ), (∀ i, 0 < α i) →
    ∀ k : ℕ, 0 < k → ∃ a : ℚ, Tendsto
      (fun N : ℕ => (((Finset.range (N + 1)).filter (collision c α k)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (a : ℝ))

theorem result : claim := by
  intro t c α _ k _
  obtain ⟨q, hq, d, hd⟩ := bracket_affine c α
  obtain ⟨M, p, hp, hmem⟩ := affine_image_tail (bracket c α) q hq d hd
  apply eventual_periodic_density (collision c α k) M p hp
  intro x hx
  unfold collision
  rw [hmem x hx]
  have hh := hmem (x + k) (by omega)
  simpa only [show x + p + k = x + k + p by omega] using and_congr Iff.rfl hh

#print axioms result

end
end D5.S3.Arith.Density.RationalBracketCollisionDensity
