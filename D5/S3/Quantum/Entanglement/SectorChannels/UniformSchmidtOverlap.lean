/- GID: D5/S3/Quantum/Entanglement/SectorChannels/UniformSchmidtOverlap
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/UniformSchmidtOverlap
   mirror-E: none(waiver:exact-finite-channel-optimization)
   anchors: []
   utility: none
   digest: Finite coherent matched Born overlaps obey a spectral upper bound and an explicit private-randomness lower bound at arbitrary rank and output size. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap

open scoped BigOperators

namespace RTCriticalOverlap

private def overlap {ι : Type*} (s : Finset ι) (c : ℝ) (q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, min c (q i)

end RTCriticalOverlap

open scoped BigOperators

namespace RTCriticalOverlap

/-- One heavy atom at normalized weight x². Choose between adjacent integer
label counts. An exclusive block of h labels contributes min(h,x²/h)
in units of the per-label cap. The chosen h fits inside the atom's own
mass budget and loses at most sqrt(2), not a factor of two. -/
private theorem heavy_adjacent_allocation_of_scale (k : ℕ) (x s : ℝ) (hk : 1 ≤ k)
    (hkx : (k : ℝ) ≤ x) (hxk : x ≤ (k : ℝ)+1) (hs : 0 ≤ s)
    (hscale : (k:ℝ)+1 ≤ s^2 * (k:ℝ)) :
    ∃ h : ℕ, (h=k ∨ h=k+1) ∧ 0<h ∧ (h:ℝ) ≤ x^2 ∧
      x ≤ s * min (h:ℝ) (x^2 / (h:ℝ)) := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hx0 : 0 < x := hk0.trans_le hkx
  have hx2 : (k:ℝ)^2 ≤ x^2 := pow_le_pow_left₀ hk0.le hkx 2
  by_cases hfloor : x^2 ≤ (k:ℝ)*((k:ℝ)+1)
  · refine ⟨k,Or.inl rfl,by omega,?_,?_⟩
    · exact (by nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hk1)] : (k:ℝ) ≤ (k:ℝ)^2).trans hx2
    rw [min_eq_left ((le_div_iff₀ hk0).mpr (by simpa only [pow_two] using hx2))]
    have hcomp : x^2 ≤ (s * (k:ℝ))^2 := by
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hscale hk0.le]
    by_contra! hh
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < x + s * (k:ℝ) by positivity)]
  · push Not at hfloor
    refine ⟨k+1, Or.inr rfl, by omega, ?_, ?_⟩
    · push_cast
      nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)+1 by positivity) (sub_nonneg.mpr hk1)]
    push_cast
    have hk10 : 0 < (k:ℝ)+1 := by positivity
    have hy2 : x^2 ≤ ((k:ℝ)+1)^2 := pow_le_pow_left₀ hx0.le hxk 2
    rw [min_eq_right ((div_le_iff₀ hk10).mpr (by simpa only [pow_two] using hy2))]
    rw [←mul_div_assoc, le_div_iff₀ hk10, pow_two, ←mul_assoc, mul_comm (s*x) x]
    apply mul_le_mul_of_nonneg_left _ hx0.le
    have hcomp : ((k:ℝ)+1)^2 ≤ (s * x)^2 := by
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right hscale hk10.le,
        mul_le_mul_of_nonneg_left hfloor.le (sq_nonneg s)]
    by_contra! hh
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < (k:ℝ)+1 + s*x by positivity)]

/-- Uniform sqrt(2) bound; the sharp uniform factor of this per-atom
adjacent-choice calculation occurs at k=1 and x=sqrt(2). -/
private theorem heavy_adjacent_allocation (k : ℕ) (x : ℝ) (hk : 1 ≤ k)
    (hkx : (k : ℝ) ≤ x) (hxk : x ≤ (k : ℝ)+1) :
    ∃ h : ℕ, (h=k ∨ h=k+1) ∧ 0<h ∧ (h:ℝ) ≤ x^2 ∧
      x ≤ Real.sqrt 2 * min (h:ℝ) (x^2 / (h:ℝ)) := by
  apply heavy_adjacent_allocation_of_scale k x (Real.sqrt 2) hk hkx hxk (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- Secant lower bound for a light bin, normalized to unit capacity. -/
private theorem light_cap_chord {r x : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hlo : r ≤ x) (hhi : x ≤ r+1) : (1-r)*x+r^2 ≤ min 1 x := by
  apply le_min
  · nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hhi)]
  · nlinarith [mul_nonneg hr (sub_nonneg.mpr hlo)]

/-- Final bin loads within one unit of their minimum retain at least
three quarters of their total mass after capping at one, whenever
total mass does not exceed the total capacity. -/
private theorem light_overlap_chord {ι : Type*} (s : Finset ι) (load : ι → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hlo : ∀ i ∈ s, r≤load i) (hhi : ∀ i ∈ s, load i≤r+1)
    (hcap : (∑ i ∈ s, load i) ≤ (s.card:ℝ)) :
    (3/4:ℝ)*(∑ i ∈ s, load i) ≤ overlap s 1 load := by
  let S : ℝ := ∑ i ∈ s, load i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => hr.trans (hlo i hi))
  calc
    (3/4:ℝ)*S ≤ (1-r+r^2)*S := by
      apply mul_le_mul_of_nonneg_right _ hS
      nlinarith [sq_nonneg (r-(1/2))]
    _ ≤ (1-r)*S+(s.card:ℝ)*r^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hcap (sq_nonneg r)]
    _ = ∑ i ∈ s, ((1-r)*load i+r^2) := by
      simp only [S,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    _ ≤ overlap s 1 load := Finset.sum_le_sum fun i hi => light_cap_chord hr hr1 (hlo i hi) (hhi i hi)

/-- A least-load update preserves the diameter at most one. -/
private theorem light_update_diameter {ι : Type*} [DecidableEq ι] (load : ι → ℝ)
    (pick : ι) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hmin : ∀ j, load pick ≤ load j) (hdiam : ∀ i j, load i ≤ load j+1) :
    ∀ i j, (load i + if i=pick then w else 0) ≤ (load j + if j=pick then w else 0)+1 := by
  intro i j
  by_cases hi : i=pick <;> by_cases hj : j=pick
  · simp [hi,hj]
  · simp only [hi,hj,ite_true,ite_false,add_zero]
    linarith [hmin j]
  · simp only [hi,hj,ite_true,ite_false,add_zero]
    subst j
    linarith [hdiam i pick]
  · simpa only [hi,hj,ite_false,add_zero] using hdiam i j

end RTCriticalOverlap

open scoped BigOperators

namespace RTCriticalOverlap

private def groupLoad {κ ι : Type*} [DecidableEq ι] (s : Finset κ)
    (w : κ → ℝ) (assign : κ → ι) (i : ι) : ℝ :=
  ∑ a ∈ s, if assign a = i then w a else 0

private theorem sum_groupLoad {κ ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset κ)
    (w : κ → ℝ) (assign : κ → ι) :
    (∑ i : ι, groupLoad s w assign i) = ∑ a ∈ s, w a := by
  unfold groupLoad
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => by simp)

/-- There is an actual common deterministic label map. In normalized units
all weights are at most one; least-load assignment ensures every pair of
terminal loads differs by at most one. -/
private theorem greedy_assignment_diameter {κ ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (s : Finset κ) (w : κ → ℝ)
    (hw0 : ∀ a ∈ s, 0 ≤ w a) (hw1 : ∀ a ∈ s, w a ≤ 1) :
    ∃ assign : κ → ι, ∀ i j, groupLoad s w assign i ≤ groupLoad s w assign j + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => Classical.choice inferInstance, by simp [groupLoad]⟩
  | @insert a s ha ih =>
    have hmem : a ∈ insert a s := Finset.mem_insert_self _ _
    obtain ⟨assign,hdiam⟩ := ih
      (fun b hb => hw0 b (Finset.mem_insert_of_mem hb))
      (fun b hb => hw1 b (Finset.mem_insert_of_mem hb))
    let load := groupLoad s w assign
    obtain ⟨pick, _, hp⟩ := Finset.exists_min_image (Finset.univ : Finset ι) load Finset.univ_nonempty
    let assign' := fun b => if b=a then pick else assign b
    have heq (i : ι) :
        groupLoad (insert a s) w assign' i = load i + (if i=pick then w a else 0) := by
      simp only [groupLoad,load]
      rw [Finset.sum_insert ha]
      have hS : (∑ b ∈ s, if assign' b = i then w b else 0) =
          ∑ b ∈ s, if assign b = i then w b else 0 := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hn : b ≠ a := by
          intro h
          exact ha (h ▸ hb)
        simp [assign',hn]
      rw [hS, show assign' a = pick by simp [assign']]
      by_cases e : i=pick
      · subst i
        simp only [ite_true]
        exact add_comm _ _
      · simp [e,Ne.symm e]
    refine ⟨assign',fun i j => ?_⟩
    rw [heq i,heq j]
    exact light_update_diameter load pick (w a) (hw0 a hmem) (hw1 a hmem)
      (fun j => hp j (Finset.mem_univ _)) hdiam i j

/-- Constructive light-overlap lower bound on an arbitrary nonempty finite
label set, with no shared seed. -/
private theorem light_greedy_overlap {κ ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (s : Finset κ) (w : κ → ℝ)
    (hw0 : ∀ a ∈ s, 0 ≤ w a) (hw1 : ∀ a ∈ s, w a ≤ 1)
    (hcap : (∑ a ∈ s, w a) ≤ (Fintype.card ι : ℝ)) :
    ∃ assign : κ → ι, (3/4:ℝ)*(∑ a ∈ s, w a) ≤ overlap Finset.univ 1 (groupLoad s w assign) := by
  classical
  obtain ⟨assign, hd⟩ := greedy_assignment_diameter (ι:=ι) s w hw0 hw1
  let load := groupLoad s w assign
  obtain ⟨pick, _, hp⟩ := Finset.exists_min_image (Finset.univ : Finset ι) load Finset.univ_nonempty
  have he := sum_groupLoad s w assign
  have hnn : 0 ≤ load pick := Finset.sum_nonneg (fun a ha => by split <;> simp [hw0 a ha])
  have hmin : ∀ j, load pick ≤ load j := fun j => hp j (Finset.mem_univ _)
  have h1 : load pick ≤ 1 := by
    have hA : (Fintype.card ι : ℝ) * load pick ≤ ∑ i : ι, load i := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        (Finset.sum_le_sum (s:= (Finset.univ : Finset ι)) (fun i _ => hmin i))
    have hp0 : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    change (∑ i : ι, load i) = ∑ a ∈ s, w a at he
    rw [he] at hA
    by_contra! H
    nlinarith [hA.trans hcap, mul_pos hp0 (sub_pos.mpr H)]
  refine ⟨assign, ?_⟩
  have hc : (∑ i : ι, load i) ≤ ((Finset.univ : Finset ι).card : ℝ) := by
    simpa only [Finset.card_univ, load,he] using hcap
  have h := light_overlap_chord Finset.univ load (load pick) hnn h1
    (fun i _ => hmin i) (fun i _ => hd i pick) hc
  simpa only [load,he] using h

end RTCriticalOverlap

open scoped BigOperators

namespace RTCriticalOverlap

private noncomputable def heavyScore {ι : Type*} (h : ι → ℕ) (u : ι → ℝ) (a : ι) : ℝ :=
  min (h a : ℝ) (u a / (h a : ℝ))

/-- Integer exclusive blocks and a feasible residual light assignment, with
the sum of the actual capped contributions at least 1/sqrt(2) of the spectral
score. All weights are in units of the common uniform target cap. -/
private theorem heavy_light_plan {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ℕ) (u : ι → ℝ) (w : κ → ℝ)
    (hu : ∀ a, 1 ≤ u a) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1)
    (hmass : (∑ a, u a) + (∑ a, w a) ≤ (m:ℝ)) :
    ∃ (h : ι → ℕ) (r : ℕ) (load : Fin r → ℝ),
      (∀ a, 0 < h a ∧ (h a:ℝ) ≤ u a) ∧
      (∑ a, h a) + r = m ∧
      ((r = 0 ∧ (∑ a, w a) = 0) ∨
        ∃ assign : κ → Fin r, load = groupLoad Finset.univ w assign) ∧
      (∑ a, Real.sqrt (u a)) + (∑ a, w a) ≤
        Real.sqrt 2 * ((∑ a, heavyScore h u a) + overlap Finset.univ 1 load) := by
  classical
  have hx (a : ι) : 1 ≤ Real.sqrt (u a) := by
    simpa using Real.sqrt_le_sqrt (hu a)
  have H (a : ι) : ∃ n : ℕ, (0 < n ∧ (n:ℝ) ≤ u a) ∧
      Real.sqrt (u a) ≤ Real.sqrt 2 * min (n:ℝ) (u a/(n:ℝ)) := by
    let k := Nat.floor (Real.sqrt (u a))
    have hk : 1 ≤ k := (Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).2 (by simpa using hx a)
    obtain ⟨n,_,hn,hbudget,hscore⟩ := heavy_adjacent_allocation k (Real.sqrt (u a))
      hk (Nat.floor_le (Real.sqrt_nonneg _)) (Nat.lt_floor_add_one _).le
    rw [Real.sq_sqrt (by linarith [hu a])] at hbudget hscore
    exact ⟨n,⟨hn,hbudget⟩,hscore⟩
  choose h hL hS using H
  let d : ℕ := ∑ a, h a
  let r : ℕ := m-d
  let W : ℝ := ∑ a, w a
  have hW : 0 ≤ W := Finset.sum_nonneg (fun a _ => hw0 a)
  have hd : (d:ℝ) ≤ ∑ a, u a := by
    dsimp [d]
    push_cast
    exact Finset.sum_le_sum (fun a _ => (hL a).2)
  have hdm : d ≤ m := by
    exact_mod_cast (show (d:ℝ) ≤ m by linarith)
  have hcount : d+r=m := by dsimp [r]; omega
  have hc' : (d:ℝ)+(r:ℝ)=m := by exact_mod_cast hcount
  have hcap : W ≤ r := by dsimp [W] at *; linarith
  have hheavy : (∑ a, Real.sqrt (u a)) ≤ Real.sqrt 2 * ∑ a, heavyScore h u a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => hS a)
  have hs2 : (4/3:ℝ) ≤ Real.sqrt 2 := by
    have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have h0 := Real.sqrt_nonneg (2:ℝ)
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 4/3+Real.sqrt 2 by positivity)]
  have hfinish (load : Fin r → ℝ) (hl : (3/4:ℝ)*W ≤ overlap Finset.univ 1 load) :
      (∑ a, Real.sqrt (u a)) + W ≤
        Real.sqrt 2 * ((∑ a, heavyScore h u a) + overlap Finset.univ 1 load) := by
    rw [mul_add]
    have S : W ≤ Real.sqrt 2 * overlap Finset.univ 1 load := by
      calc
        W = (4/3:ℝ)*((3/4:ℝ)*W) := by ring
        _ ≤ Real.sqrt 2*((3/4:ℝ)*W) := mul_le_mul_of_nonneg_right hs2 (by positivity)
        _ ≤ Real.sqrt 2 * overlap Finset.univ 1 load :=
          mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)
    exact add_le_add hheavy S
  by_cases hr : r=0
  · have hWz : W=0 := by rw [hr, Nat.cast_zero] at hcap; linarith
    refine ⟨h,r,fun _ => 0,hL,hcount,Or.inl ⟨hr,hWz⟩,hfinish _ ?_⟩
    simp [hWz,overlap]
  · let : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
    obtain ⟨assign, hlight⟩ := light_greedy_overlap (ι := Fin r) Finset.univ w
      (fun a _ => hw0 a) (fun a _ => hw1 a) (by simpa [W] using hcap)
    exact ⟨h,r,groupLoad Finset.univ w assign,hL,hcount,
      Or.inr ⟨assign,rfl⟩,hfinish _ hlight⟩

end RTCriticalOverlap

open scoped BigOperators

namespace RTCriticalOverlap

/-- A certified target label consists of a label in one heavy atom's
exclusive block, or one of the remaining light labels. -/
private abbrev Labels {ι : Type*} (h : ι → ℕ) (r : ℕ) :=
  (Σ a, Fin (h a)) ⊕ Fin r

private theorem labels_card {ι : Type*} [Fintype ι] (h : ι → ℕ) (r : ℕ) :
    Fintype.card (Labels h r) = (∑ a, h a)+r := by simp [Labels]

/-- Both parties independently sample this conditional response after
observing the same heavy Schmidt index. -/
private noncomputable def heavyResponse {ι : Type*} [DecidableEq ι]
    (h : ι → ℕ) (r : ℕ) (a : ι) : Labels h r → ℝ
  | .inl b => if b.1 = a then 1 / (h a : ℝ) else 0
  | .inr _ => 0

/-- The common deterministic response for a light Schmidt index. -/
private def lightResponse {ι κ : Type*}
    (h : ι → ℕ) (r : ℕ) (assign : κ → Fin r) (a : κ) : Labels h r → ℝ
  | .inl _ => 0
  | .inr l => if assign a = l then 1 else 0

private theorem heavy_response_stochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℕ) (r : ℕ) (a : ι) (hpos : 0 < h a) :
    (∀ l, 0 ≤ heavyResponse h r a l) ∧ (∑ l, heavyResponse h r a l) = 1 := by
  constructor
  · rintro (b | l)
    · unfold heavyResponse; split <;> positivity
    · exact le_rfl
  · rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [heavyResponse,Finset.sum_const_zero,add_zero]
    simp [show (h a : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hpos]

private theorem light_response_stochastic {ι κ : Type*} [Fintype ι]
    (h : ι → ℕ) (r : ℕ) (assign : κ → Fin r) (a : κ) :
    (∀ l, 0 ≤ lightResponse h r assign a l) ∧ (∑ l, lightResponse h r assign a l) = 1 := by
  constructor
  · rintro (b | l)
    · exact le_rfl
    · change 0 ≤ if assign a = l then (1:ℝ) else 0
      split <;> norm_num
  · simp [Fintype.sum_sum_type, lightResponse]

/-- Normalized diagonal law of the two independent draws, conditional on
the shared Schmidt outcome. -/
private noncomputable def privateDiagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (h : ι → ℕ) (r : ℕ) (u : ι → ℝ) (w : κ → ℝ)
    (assign : κ → Fin r) (l : Labels h r) : ℝ :=
  (∑ a, u a*(heavyResponse h r a l)^2) +
    (∑ a, w a*(lightResponse h r assign a l)^2)

private theorem privateDiagonal_heavy {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (h : ι → ℕ) (r : ℕ) (u : ι → ℝ) (w : κ → ℝ)
    (assign : κ → Fin r) (a : ι) (i : Fin (h a)) :
    privateDiagonal h r u w assign (.inl ⟨a,i⟩) = u a/(h a:ℝ)^2 := by
  unfold privateDiagonal
  simp only [heavyResponse, lightResponse,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,
    Finset.sum_const_zero, add_zero, ite_pow]
  simp [mul_ite,div_eq_mul_inv]

private theorem privateDiagonal_light {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (h : ι → ℕ) (r : ℕ) (u : ι → ℝ) (w : κ → ℝ)
    (assign : κ → Fin r) (i : Fin r) :
    privateDiagonal h r u w assign (.inr i) = groupLoad Finset.univ w assign i := by
  unfold privateDiagonal groupLoad
  simp only [heavyResponse, lightResponse,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,
    Finset.sum_const_zero, zero_add,ite_pow,one_pow,mul_ite,mul_one]

private theorem privateDiagonal_overlap {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (h : ι → ℕ) (r : ℕ) (u : ι → ℝ) (w : κ → ℝ)
    (hpos : ∀ a, 0 < h a) (assign : κ → Fin r) :
    overlap Finset.univ 1 (privateDiagonal h r u w assign) =
      (∑ a, heavyScore h u a) + overlap Finset.univ 1 (groupLoad Finset.univ w assign) := by
  unfold overlap
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [privateDiagonal_heavy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have h0 : (0:ℝ)< h a := by exact_mod_cast hpos a
    rw [mul_min_of_nonneg _ _ h0.le, mul_one, heavyScore]
    congr 1
    field_simp [h0.ne']
  · exact Finset.sum_congr rfl (fun _ _ => by rw [privateDiagonal_light])

/-- Attained scalar overlap by actual independent private draws, on a literal
label type of cardinality m. Strictly positive light probabilities avoid
having to define a response for a zero-mass atom when no labels remain. -/
private theorem private_label_protocol {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (m : ℕ) (u : ι → ℝ) (w : κ → ℝ)
    (hu : ∀ a, 1 ≤ u a) (hw0 : ∀ a, 0 < w a) (hw1 : ∀ a, w a ≤ 1)
    (hmass : (∑ a, u a) + (∑ a, w a) ≤ (m:ℝ)) :
    ∃ (h : ι → ℕ) (r : ℕ) (assign : κ → Fin r),
      Fintype.card (Labels h r) = m ∧
      (∀ a, (∀ l, 0 ≤ heavyResponse h r a l) ∧ (∑ l, heavyResponse h r a l) = 1) ∧
      (∀ a, (∀ l, 0 ≤ lightResponse h r assign a l) ∧ (∑ l, lightResponse h r assign a l) = 1) ∧
      (∑ a, Real.sqrt (u a)) + (∑ a, w a) ≤ Real.sqrt 2 *
        overlap Finset.univ 1 (privateDiagonal h r u w assign) := by
  obtain ⟨h,r,load,hpos,hcount,hl,hgain⟩ := heavy_light_plan m u w hu
    (fun a => (hw0 a).le) hw1 hmass
  have ha : ∃ assign : κ → Fin r, load = groupLoad Finset.univ w assign := by
    rcases hl with ⟨hz,hs⟩ | ha
    · have hwz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => (hw0 a).le)).mp hs
      refine ⟨fun a => False.elim ((hw0 a).ne' (hwz a (Finset.mem_univ _))), ?_⟩
      ext i
      exact False.elim (by have hi := i.isLt; omega)
    · exact ha
  obtain ⟨assign,hload⟩ := ha
  refine ⟨h,r,assign,(labels_card h r).trans hcount,
    (fun a => heavy_response_stochastic h r a (hpos a).1),
    (fun a => light_response_stochastic h r assign a),?_⟩
  rw [privateDiagonal_overlap h r u w (fun a => (hpos a).1) assign,←hload]
  exact hgain

end RTCriticalOverlap

open scoped BigOperators

namespace RTCriticalOverlap

/-- Spectral overlap score for positive Schmidt probabilities. -/
noncomputable def spectralScore {τ : Type*} [Fintype τ] (m : ℕ) (p : τ → ℝ) : ℝ :=
  ∑ a, min (p a) (Real.sqrt (p a/(m:ℝ)))

/-- Exact finite probability lower construction on the requested `Fin m`
labels. A single stochastic response is used by both parties, with
independent private draws conditional on the common Schmidt readout.
The multiplier sqrt(2) applies for every spectrum and output size. -/
private theorem uniform_protocol_lower {τ : Type*} [Fintype τ] (m : ℕ) (hm : 0<m)
    (p : τ → ℝ) (hp : ∀ a, 0 < p a) (hsum : (∑ a, p a) = 1) :
    ∃ f : τ → Fin m → ℝ,
      (∀ a l, 0 ≤ f a l) ∧ (∀ a, (∑ l, f a l) = 1) ∧
      spectralScore m p ≤ Real.sqrt 2 *
        overlap Finset.univ (1/(m:ℝ)) (fun l => ∑ a, p a*(f a l)^2) := by
  classical
  let M : ℝ := m
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hm
  let big : τ → Prop := fun a => 1 ≤ M*p a
  let : DecidablePred big := Classical.decPred _
  let H := {a // big a}
  let L := {a // ¬big a}
  let u : H → ℝ := fun a => M*p a
  let w : L → ℝ := fun a => M*p a
  have hmass : (∑ a, u a) + (∑ a, w a) = M := by
    change (∑ a : {a // big a}, M*p a) + (∑ a : {a // ¬big a}, M*p a) = M
    rw [Fintype.sum_subtype_add_sum_subtype big (fun a => M*p a), ← Finset.mul_sum, hsum, mul_one]
  obtain ⟨h,r,assign,hcard,hheavy,hlight,hgain⟩ := private_label_protocol m u w
    (fun a => a.property)
    (fun a => mul_pos hM (hp a))
    (fun a => le_of_lt (lt_of_not_ge a.property)) (by rw [hmass])
  let K := Labels h r
  let rho : τ → K → ℝ := fun a l =>
    if ha : big a then heavyResponse h r ⟨a,ha⟩ l else lightResponse h r assign ⟨a,ha⟩ l
  have hrho (a : τ) : (∀ l, 0 ≤ rho a l) ∧ (∑ l, rho a l) = 1 := by
    by_cases ha : big a
    · simpa only [rho,dite_eq_left ha] using hheavy ⟨a,ha⟩
    · simpa only [rho,dite_eq_right ha] using hlight ⟨a,ha⟩
  let e : K ≃ Fin m := Fintype.equivFinOfCardEq hcard
  let f : τ → Fin m → ℝ := fun a l => rho a (e.symm l)
  refine ⟨f,(fun a l => (hrho a).1 _),?_,?_⟩
  · intro a
    dsimp [f]
    rw [Equiv.sum_comp]
    exact (hrho a).2
  have hscore (a : τ) : M*Real.sqrt (p a/M) = Real.sqrt (M*p a) := by
    calc
      M*Real.sqrt (p a/M) = Real.sqrt (M^2)*Real.sqrt (p a/M) := by
        rw [Real.sqrt_sq hM.le]
      _ = Real.sqrt (M^2*(p a/M)) := (Real.sqrt_mul (sq_nonneg _) _).symm
      _ = Real.sqrt (M*p a) := by congr 1; field_simp
  have hspec : M * spectralScore m p = (∑ a, Real.sqrt (u a)) + (∑ a, w a) := by
    unfold spectralScore
    rw [Finset.mul_sum, ← Fintype.sum_subtype_add_sum_subtype big
      (fun a => M * min (p a) (Real.sqrt (p a/(m:ℝ))))]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      change M * min (p a) (Real.sqrt (p a/M)) = Real.sqrt (M*p a)
      rw [mul_min_of_nonneg _ _ hM.le, hscore]
      apply min_eq_right
      have h : (1:ℝ) ≤ M*p a := a.property
      by_contra! H
      have t := Real.sq_sqrt (mul_nonneg hM.le (hp a).le)
      nlinarith [mul_pos (sub_pos.mpr H)
        (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (M*p a)) (mul_pos hM (hp a))),
        mul_nonneg (mul_nonneg hM.le (hp a).le) (sub_nonneg.mpr h)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      change M * min (p a) (Real.sqrt (p a/M)) = M*p a
      rw [mul_min_of_nonneg _ _ hM.le, hscore]
      apply min_eq_left
      have h : M*p a ≤ 1 := (lt_of_not_ge a.property).le
      by_contra! H
      have t := Real.sq_sqrt (mul_nonneg hM.le (hp a).le)
      nlinarith [mul_pos (sub_pos.mpr H)
        (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (M*p a)) (mul_pos hM (hp a))),
        mul_nonneg (mul_nonneg hM.le (hp a).le) (sub_nonneg.mpr h)]
  have hd (l : K) : M * (∑ a, p a*(rho a l)^2) =
      privateDiagonal h r u w assign l := by
    rw [Finset.mul_sum, ← Fintype.sum_subtype_add_sum_subtype big
      (fun a => M*(p a*(rho a l)^2))]
    unfold privateDiagonal
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [u,rho,dite_eq_left a.property,mul_assoc]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [w,rho,dite_eq_right a.property,mul_assoc]
  have hover : M * overlap Finset.univ (1/(m:ℝ))
      (fun l => ∑ a, p a*(f a l)^2) =
        overlap Finset.univ 1 (privateDiagonal h r u w assign) := by
    unfold overlap
    rw [Finset.mul_sum]
    have ht :
        (∑ l : Fin m, M * min (1/(m:ℝ)) (∑ a, p a*(f a l)^2)) =
          ∑ l : K, M * min (1/M) (∑ a, p a*(rho a l)^2) :=
      Equiv.sum_comp e.symm (fun l => M * min (1/M) (∑ a, p a*(rho a l)^2))
    rw [ht]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_min_of_nonneg _ _ hM.le, hd]
    rw [mul_one_div_cancel hM.ne']
  apply le_of_mul_le_mul_left ?_ hM
  rw [hspec, ←mul_left_comm,hover]
  exact hgain

end RTCriticalOverlap

open scoped BigOperators

namespace RTOverlap

private noncomputable def capMass {ι : Type*} (s : Finset ι) (c : ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i ∈ s, min (c^2) ((z i)^2)

private theorem two_substate_cap_sharp {ι : Type*} (s : Finset ι)
    (c L H : ℝ) (u v z : ι → ℝ)
    (hc : 0 ≤ c)
    (hv : ∀ i ∈ s, 0 ≤ v i)
    (hz : ∀ i ∈ s, 0 ≤ z i) (htri : ∀ i ∈ s, z i ≤ u i + v i)
    (hl : ∑ i ∈ s, (u i)^2 ≤ L)
    (hh : c * (∑ i ∈ s, v i) ≤ H) :
    let O := capMass s c z
    3 * O ≤ 4 * (L+H) := by
  let w : ι → ℝ := fun i => min c (z i)
  let O : ℝ := capMass s c z
  have hn (i : ι) (hi : i ∈ s) : 0 ≤ w i := le_min hc (hz i hi)
  have hs (i : ι) (hi : i ∈ s) : (w i)^2 = min (c^2) ((z i)^2) := by
    change (min c (z i))^2 = _
    rcases le_total c (z i) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hc (hz i hi))])]
    · rw [min_eq_right h, min_eq_right (by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hc (hz i hi))])]
  have hO : (∑ i ∈ s, (w i)^2) = O := Finset.sum_congr rfl hs
  have ht (i : ι) (hi : i ∈ s) : w i ^ 2 ≤ w i * u i + c * v i := by
    have hwu : w i ≤ u i + v i := (min_le_right _ _).trans (htri i hi)
    have a := mul_le_mul_of_nonneg_left hwu (hn i hi)
    have b := mul_le_mul_of_nonneg_right (min_le_left c (z i)) (hv i hi)
    change w i * v i ≤ c * v i at b
    nlinarith only [a,b]
  have sharp : 3 * O ≤ 4 * (L+H) := by
    have hh' (i : ι) (hi : i ∈ s) : 3*(w i)^2 ≤ 4*((u i)^2 + c*v i) :=
      by nlinarith only [ht i hi, sq_nonneg (2*u i-w i)]
    have zsum := Finset.sum_le_sum hh'
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at zsum
    rw [hO] at zsum
    exact zsum.trans (mul_le_mul_of_nonneg_left (add_le_add hl hh) (by positivity))
  exact sharp

end RTOverlap

open scoped BigOperators ComplexConjugate
namespace RTOverlap

noncomputable def lsquare {J : Type*} [Fintype J] (v : J → ℂ) : ℝ :=
  ∑ i, ‖v i‖^2

noncomputable def lnorm {J : Type*} [Fintype J] (v : J → ℂ) : ℝ :=
  Real.sqrt (lsquare v)

private lemma lsquare_nonneg {J : Type*} [Fintype J] (v : J → ℂ) : 0 ≤ lsquare v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma lnorm_nonneg {J : Type*} [Fintype J] (v : J → ℂ) : 0 ≤ lnorm v :=
  Real.sqrt_nonneg _

private lemma lnorm_sq {J : Type*} [Fintype J] (v : J → ℂ) : (lnorm v)^2 = lsquare v :=
  Real.sq_sqrt (lsquare_nonneg v)

private lemma lnorm_zero {J : Type*} [Fintype J] : lnorm (0 : J → ℂ) = 0 := by
  simp [lnorm, lsquare]

private lemma lnorm_add_le {J : Type*} [Fintype J] (v w : J → ℂ) :
    lnorm (v+w) ≤ lnorm v + lnorm w := by
  have hs : lsquare (v+w) ≤ ∑ i, (‖v i‖ + ‖w i‖)^2 := by
    change (∑ i, ‖v i+w i‖^2) ≤ _
    exact Finset.sum_le_sum fun i _ => by
      gcongr
      exact norm_add_le _ _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖v i‖) (fun i => ‖w i‖)
  change (∑ i, ‖v i‖ * ‖w i‖) ≤ lnorm v * lnorm w at hcs
  unfold lnorm at *
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,hs.trans ?_⟩
  simp only [add_sq, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  change lsquare v + 2 * (∑ i, ‖v i‖ * ‖w i‖) + lsquare w ≤ _
  nlinarith only [hcs,Real.sq_sqrt (lsquare_nonneg v),Real.sq_sqrt (lsquare_nonneg w)]

private lemma lnorm_finset_sum_le {J S : Type*} [Fintype J]
    (s : Finset S) (v : S → J → ℂ) :
    lnorm (∑ a ∈ s, v a) ≤ ∑ a ∈ s, lnorm (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lnorm_zero]
  | insert a s ha hi =>
    simp only [Finset.sum_insert ha]
    exact (lnorm_add_le _ _).trans (add_le_add_right hi _)

private lemma lnorm_smul {J : Type*} [Fintype J] (a : ℂ) (f : J → ℂ) :
    lnorm (fun j => a * f j) = ‖a‖ * lnorm f := by
  unfold lnorm lsquare
  simp only [Complex.norm_mul, mul_pow, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg ‖a‖),
    Real.sqrt_sq (norm_nonneg a)]

private lemma lnorm_tensor {J K : Type*} [Fintype J] [Fintype K]
    (v : J → ℂ) (w : K → ℂ) :
    lnorm (fun jk : J × K => v jk.1 * w jk.2) = lnorm v * lnorm w := by
  unfold lnorm lsquare
  simp only [Fintype.sum_prod_type, Complex.norm_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  exact Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _) _

/-- Finite left/right local Kraus arrays expressed by their isometric column
condition. These columns permit arbitrary coherent effects; no diagonal or
Schmidt-measurement restriction appears. -/
structure LocalColumns (I O K : Type*) [DecidableEq I] [Fintype O] [Fintype K] where
  entry : I → O → K → ℂ
  gram : ∀ a b : I, (∑ i, ∑ k, conj (entry a i k) * entry b i k) =
    (if a = b then 1 else 0 : ℂ)


private def reAdd : ℂ →+ ℝ := ⟨⟨Complex.re,rfl⟩,Complex.add_re⟩

private lemma lsquare_as_gram {J : Type*} [Fintype J] (f : J → ℂ) :
    lsquare f = (∑ i, conj (f i) * f i).re := by
  have h : (∑ i, conj (f i) * f i) = (∑ i, (Complex.normSq (f i) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, Complex.mul_conj]
  rw [h]
  change lsquare f = reAdd (∑ i, (Complex.normSq (f i) : ℂ))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.sq_norm (f i)

private lemma columns_isometry {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (F : I → J → ℂ)
    (h : ∀ a b, (∑ j, conj (F a j) * F b j) = (if a = b then 1 else 0 : ℂ))
    (x : I → ℂ) :
    lsquare (fun j => ∑ a, x a * F a j) = lsquare x := by
  have he (j : J) :
      conj (∑ a, x a * F a j) * (∑ b, x b * F b j) =
        ∑ a, ∑ b, (conj (x a) * x b) * (conj (F a j) * F b j) := by
    rw [map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul]
    ring
  rw [lsquare_as_gram, lsquare_as_gram x]
  simp only [he]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, h]
  simp

private lemma local_col_norm {I O K : Type*} [DecidableEq I] [Fintype O] [Fintype K]
    (A : LocalColumns I O K) (a : I) :
    (∑ i, (lnorm (A.entry a i))^2) = 1 := by
  simp only [lnorm_sq,lsquare_as_gram]
  change (∑ i, reAdd (∑ k, conj (A.entry a i k) * A.entry a i k)) = _
  rw [← map_sum, A.gram, ite_eq_left rfl]
  rfl

private lemma joint_columns_gram {I O K V : Type*} [DecidableEq I]
    [Fintype O] [Fintype K] [Fintype V]
    (A : LocalColumns I O K) (B : LocalColumns I O V) (a b : I) :
    (∑ ikjl : (O × K) × (O × V),
      conj (A.entry a ikjl.1.1 ikjl.1.2 * B.entry a ikjl.2.1 ikjl.2.2) *
       (A.entry b ikjl.1.1 ikjl.1.2 * B.entry b ikjl.2.1 ikjl.2.2)) =
       (if a=b then 1 else 0 : ℂ) := by
  have h :
      (∑ ikjl : (O × K) × (O × V),
      conj (A.entry a ikjl.1.1 ikjl.1.2 * B.entry a ikjl.2.1 ikjl.2.2) *
       (A.entry b ikjl.1.1 ikjl.1.2 * B.entry b ikjl.2.1 ikjl.2.2)) =
      (∑ i, ∑ k, conj (A.entry a i k) * A.entry b i k) *
      (∑ j, ∑ l, conj (B.entry a j l) * B.entry b j l) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    ring
  rw [h,A.gram,B.gram]
  split <;> simp


noncomputable def bornVector {I O K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype K] [Fintype V]
    (A : LocalColumns I O K) (B : LocalColumns I O V) (x : I → ℂ)
    (i j : O) (kl : K × V) : ℂ :=
  ∑ a, x a * (A.entry a i kl.1 * B.entry a j kl.2)

private lemma born_total {I O K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype K] [Fintype V]
    (A : LocalColumns I O K) (B : LocalColumns I O V) (x : I → ℂ) :
    (∑ i, ∑ j, (lnorm (bornVector A B x i j))^2) = lsquare x := by
  have h := columns_isometry (fun a (q : (O × K) × (O × V)) =>
    A.entry a q.1.1 q.1.2 * B.entry a q.2.1 q.2.2)
    (joint_columns_gram A B) x
  simp only [lsquare, Fintype.sum_prod_type] at h
  simp only [lnorm_sq,lsquare, Fintype.sum_prod_type,bornVector]
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

private lemma matched_light_budget {I O K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype K] [Fintype V]
    (A : LocalColumns I O K) (B : LocalColumns I O V) (x : I → ℂ) :
    (∑ i, (lnorm (bornVector A B x i i))^2) ≤ lsquare x := by
  rw [← born_total A B x]
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun j => (lnorm (bornVector A B x i j))^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private lemma matched_heavy_budget {I O K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype K] [Fintype V]
    (A : LocalColumns I O K) (B : LocalColumns I O V) (x : I → ℂ) :
    (∑ i, lnorm (bornVector A B x i i)) ≤ ∑ a, ‖x a‖ := by
  have hp (i : O) : lnorm (bornVector A B x i i) ≤
      ∑ a, ‖x a‖ * (lnorm (A.entry a i) * lnorm (B.entry a i)) := by
    have he : bornVector A B x i i = (∑ a, fun kl : K × V => x a * (A.entry a i kl.1 * B.entry a i kl.2)) := by
      ext kl
      simp [bornVector, Finset.sum_apply]
    rw [he]
    calc
      _ ≤ ∑ a, lnorm (fun kl : K × V => x a * (A.entry a i kl.1 * B.entry a i kl.2)) :=
        lnorm_finset_sum_le _ _
      _ = _ := by simp only [lnorm_smul,lnorm_tensor]
  have hcol (a : I) : (∑ i, lnorm (A.entry a i) * lnorm (B.entry a i)) ≤ 1 := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => lnorm (A.entry a i)) (fun i => lnorm (B.entry a i))
    rw [local_col_norm A a,local_col_norm B a, Real.sqrt_one,mul_one] at h
    exact h
  calc
    _ ≤ ∑ i, ∑ a, ‖x a‖ * (lnorm (A.entry a i) * lnorm (B.entry a i)) :=
      Finset.sum_le_sum fun i _ => hp i
    _ = ∑ a, ‖x a‖ * (∑ i, lnorm (A.entry a i) * lnorm (B.entry a i)) := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun a _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcol a) (norm_nonneg (x a))

/-- Fixed amplitudes multiplexed through two arbitrary local isometric
columns with no common seed. Exact coherent upper bounds for the actual
matched Born probabilities, not a diagonal-effect assumption. -/
private theorem coherent_born_cap {I O K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype K] [Fintype V]
    (A : LocalColumns I O K) (B : LocalColumns I O V)
    (x y : I → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    let L := lsquare x
    let H := c * (∑ a, ‖y a‖)
    let mass := capMass Finset.univ c (fun i => lnorm (bornVector A B (x+y) i i))
    3*mass ≤ 4*(L+H) := by
  have hadd (i : O) : bornVector A B (x+y) i i =
      bornVector A B x i i + bornVector A B y i i := by
    ext kl
    simp only [bornVector,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  exact two_substate_cap_sharp Finset.univ c _ _ _ _ _ hc
    (fun i _ => lnorm_nonneg _) (fun i _ => lnorm_nonneg _)
    (fun i _ => by rw [hadd]; exact lnorm_add_le _ _)
    (matched_light_budget A B x)
    (mul_le_mul_of_nonneg_left (matched_heavy_budget A B y) hc)


/-- Direct spectral cap for an arbitrary-rank Schmidt spectrum and all local
isometric Kraus columns. The common label set has `m+1` elements. -/
private theorem uniform_schmidt_cap {I K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Fintype V] (m : ℕ)
    (A : LocalColumns I (Fin (m+1)) K) (B : LocalColumns I (Fin (m+1)) V)
    (p : I → ℝ) (hp : ∀ a, 0 ≤ p a) :
    let t : ℝ := ((m : ℝ)+1)⁻¹
    let Iover := ∑ i : Fin (m+1), min t ((lnorm (bornVector A B (fun a => (Real.sqrt (p a) : ℂ)) i i))^2)
    let Z := ∑ a, min (p a) (Real.sqrt t * Real.sqrt (p a))
    3 * Iover ≤ 4 * Z := by
  classical
  let t : ℝ := ((m : ℝ)+1)⁻¹
  let c : ℝ := Real.sqrt t
  let r : I → ℂ := fun a => (Real.sqrt (p a) : ℂ)
  let x : I → ℂ := fun a => if p a ≤ t then r a else 0
  let y : I → ℂ := fun a => if p a ≤ t then 0 else r a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hct : c^2 = t := Real.sq_sqrt ht
  have hr : x+y = r := by
    funext a
    by_cases h : p a ≤ t <;> simp [x,y,h]
  have hnorm (a : I) : ‖r a‖ = Real.sqrt (p a) := by
    simp [r, Complex.norm_real,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hz : lsquare x + c * (∑ a, ‖y a‖) = ∑ a, min (p a) (c * Real.sqrt (p a)) := by
    unfold lsquare
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : p a ≤ t
    · have g := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg (p a))
      have h' : p a ≤ c * Real.sqrt (p a) := by
        change Real.sqrt (p a) * Real.sqrt (p a) ≤ _ at g
        simpa only [← pow_two,Real.sq_sqrt (hp a)] using g
      simp [x,y,h,hnorm,Real.sq_sqrt (hp a),min_eq_left h']
    · have hgt : t ≤ p a := le_of_lt (lt_of_not_ge h)
      have g := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hgt) (Real.sqrt_nonneg (p a))
      have h' : c * Real.sqrt (p a) ≤ p a := by
        change _ ≤ Real.sqrt (p a) * Real.sqrt (p a) at g
        simpa only [← pow_two,Real.sq_sqrt (hp a)] using g
      simp [x,y,h,hnorm,min_eq_right h']
  have h := coherent_born_cap A B x y c hc
  dsimp only at h
  rw [hz,hr] at h
  simpa only [capMass,hct] using h

end RTOverlap

open scoped BigOperators ComplexConjugate

namespace RTOverlap

/-- A common Schmidt measurement, followed by independent generation from this
stochastic row. The local environment records the original Schmidt label. -/
private noncomputable def columns_of_response {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (f : I → O → ℝ) (hf : ∀ a i, 0 ≤ f a i)
    (hs : ∀ a, (∑ i, f a i) = 1) : LocalColumns I O I where
  entry a i k := if k=a then (Real.sqrt (f a i) : ℂ) else 0
  gram := by
    intro a b
    by_cases e : a=b
    · subst b
      have he (i : O) :
          (∑ k, conj (if k=a then (Real.sqrt (f a i) : ℂ) else 0) *
            (if k=a then (Real.sqrt (f a i) : ℂ) else 0)) = (f a i : ℂ) := by
        rw [Finset.sum_eq_single a]
        · simp [Complex.conj_ofReal, ← pow_two]
          rw [← Complex.ofReal_pow,Real.sq_sqrt (hf a i)]
        · intro j _ hj
          simp [hj]
        · simp
      simp_rw [he]
      change (∑ i, Complex.ofRealHom (f a i)) = _
      rw [← map_sum,hs]
      simp
    · have he (i : O) (k : I) :
          conj (if k=a then (Real.sqrt (f a i) : ℂ) else 0) *
            (if k=b then (Real.sqrt (f b i) : ℂ) else 0) = 0 := by
        by_cases g : k=a
        · subst k
          simp [e]
        · simp [g]
      simp [he,e]

private lemma row_born_entry {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (f : I → O → ℝ) (hf : ∀ a i, 0 ≤ f a i)
    (hs : ∀ a, (∑ i, f a i) = 1) (x : I → ℂ)
    (i j : O) (k l : I) :
    bornVector (columns_of_response f hf hs) (columns_of_response f hf hs) x i j (k,l) =
      if k=l then x k * ((Real.sqrt (f k i) : ℂ) * (Real.sqrt (f k j) : ℂ)) else 0 := by
  unfold bornVector
  rw [Finset.sum_eq_single k]
  · simp [columns_of_response,eq_comm]
  · intro a _ h
    simp [columns_of_response,ne_comm.mp h]
  · simp

/-- Actual coherent Born probabilities for the canonical classical protocol.
There is no common freshly generated randomness: each side uses the same row
with private randomness, consequently the matched contribution squares it. -/
private theorem row_born_probability {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (f : I → O → ℝ) (hf : ∀ a i, 0 ≤ f a i)
    (hs : ∀ a, (∑ i, f a i) = 1) (p : I → ℝ) (hp : ∀ a, 0 ≤ p a)
    (i : O) :
    (lnorm (bornVector (columns_of_response f hf hs) (columns_of_response f hf hs)
      (fun a => (Real.sqrt (p a) : ℂ)) i i))^2 = ∑ a, p a * (f a i)^2 := by
  rw [lnorm_sq]
  unfold lsquare
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · rw [row_born_entry, ite_eq_left rfl]
    simp only [Complex.norm_mul, mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hp a), Real.sq_sqrt (hf a i)]
    ring
  · intro b _ h
    rw [row_born_entry]
    simp [ne_comm.mp h]
  · simp

end RTOverlap

open scoped BigOperators
namespace RTOverlap

private noncomputable def bornOverlap {I K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Fintype V] (m : ℕ) (p : I → ℝ)
    (A : LocalColumns I (Fin m) K) (B : LocalColumns I (Fin m) V) : ℝ :=
  ∑ i : Fin m, min (1/(m:ℝ)) ((lnorm (bornVector A B (fun a => (Real.sqrt (p a) : ℂ)) i i))^2)

private theorem uniform_native_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (hm : 0 < m) (p : I → ℝ) (hp : ∀ a, 0 < p a) (hs : (∑ a, p a) = 1) :
    let Z := RTCriticalOverlap.spectralScore m p
    (∀ (K V : ℕ) (A : LocalColumns I (Fin m) (Fin K)) (B : LocalColumns I (Fin m) (Fin V)),
      3 * bornOverlap m p A B ≤ 4 * Z) ∧
    ∃ A : LocalColumns I (Fin m) I, Z ≤ Real.sqrt 2 * bornOverlap m p A A := by
  refine ⟨?_,?_⟩
  · intro K V A B
    cases m with
    | zero => omega
    | succ m =>
      have h := uniform_schmidt_cap m A B p (fun a => (hp a).le)
      have eqv (a : I) :
          Real.sqrt (p a / ((m:ℝ)+1)) =
            Real.sqrt (((m:ℝ)+1)⁻¹) * Real.sqrt (p a) := by
        rw [div_eq_mul_inv, Real.sqrt_mul (hp a).le, mul_comm]
      simpa only [bornOverlap,RTCriticalOverlap.spectralScore,Nat.cast_succ,
        one_div, eqv] using h
  · obtain ⟨f,hf,hn,hl⟩ := RTCriticalOverlap.uniform_protocol_lower m hm p hp hs
    let A := columns_of_response f hf hn
    refine ⟨A,?_⟩
    unfold bornOverlap A
    simp only [row_born_probability f hf hn p (fun a => (hp a).le)]
    exact hl

end RTOverlap

open scoped BigOperators
open RTOverlap

/-- A finite coherent experiment with literal Kraus environments. Keeping the
observation domain fixed lets the cap parameter be changed on the very same
Born distribution, as in a decision threshold experiment. -/
structure CapExperiment where
  rank : ℕ
  labels : ℕ
  leftEnv : ℕ
  rightEnv : ℕ
  spectrum : Fin rank → ℝ
  left : LocalColumns (Fin rank) (Fin labels) (Fin leftEnv)
  right : LocalColumns (Fin rank) (Fin labels) (Fin rightEnv)

noncomputable def measuredCap (n : ℕ) (x : CapExperiment) : ℝ :=
  ∑ i : Fin x.labels, min (1 / ((n:ℝ)+1))
    ((lnorm (bornVector x.left x.right (fun a => (Real.sqrt (x.spectrum a) : ℂ)) i i))^2)

def UniformCapLaw (n : ℕ) (observed : CapExperiment → ℝ) : Prop :=
  ∀ (r : ℕ) (p : Fin r → ℝ), (∀ a, 0 < p a) → (∑ a, p a) = 1 →
    let Z := RTCriticalOverlap.spectralScore (n+1) p
    (∀ (K V : ℕ) (A : LocalColumns (Fin r) (Fin (n+1)) (Fin K))
      (B : LocalColumns (Fin r) (Fin (n+1)) (Fin V)),
      3 * observed ⟨r,n+1,K,V,p,A,B⟩ ≤ 4 * Z) ∧
    ∃ A : LocalColumns (Fin r) (Fin (n+1)) (Fin r),
      Z ≤ Real.sqrt 2 * observed ⟨r,n+1,r,r,p,A,A⟩

theorem uniform_matched_overlap : ∀ n : ℕ,
    let observed := measuredCap n
    UniformCapLaw n observed := by
  intro n observed r p hp hs
  simpa only [observed,bornOverlap,measuredCap,Nat.cast_succ] using
    uniform_native_bounds (n+1) (by omega) p hp hs

#print axioms uniform_matched_overlap
end D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap
