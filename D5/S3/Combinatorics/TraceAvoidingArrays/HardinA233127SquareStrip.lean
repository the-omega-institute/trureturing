/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Hardin's recurrence for literal normalized six-column square strips. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only.
Declaration names use the D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip namespace.
Cross-module consumers retain that namespace.
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
valid_next: proof_shape=bind-only; consumers=v_eq_w
initial_valid: proof_shape=bind-only; consumers=a_eq_w
first_fibres: proof_shape=bind-only; consumers=initial_counts
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w
w: proof_shape=bind-only; consumers=shifted_count
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=shifted_count
distribution: proof_shape=bind-only; consumers=distribution_step
distribution_step: proof_shape=bind-only; consumers=shifted_count
shifted_count: proof_shape=bind-only; consumers=result
distribution_relation: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result (#28649)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Certificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Lean.Elab.Tactic.Omega

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233254TriangleStrip (Row rowLegal)
open HardinA233255PairTransfer (Boundary)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible
private abbrev total := widthTotal rowLegal labels

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

private theorem valid_next (s : Seen) (c : Row)
    (hs : s.1 = true ∨ ∃ i, c i = 1) (hc : rowLegal c ∧ good s c) :
    Valid (finish s c) (labels c) := by
  refine ⟨HardinA233175PairStrip.finish_fst s c |>.mpr hs, ?_, ?_⟩
  · intro j
    exact (colour_bond_iff _ _).mp (hc.1 j)
  · intro ht j
    have htwo : ∀ i, c i ≠ 2 := by
      intro i hi
      have hh := (HardinA233175PairStrip.finish_snd s c).mpr (Or.inr ⟨i, hi⟩)
      simp [ht] at hh
    have hstate : s.2 ≠ true := by
      intro hi
      have hh := (HardinA233175PairStrip.finish_snd s c).mpr (Or.inl hi)
      simp [ht] at hh
    have hthree : ∀ i, c i ≠ 3 := by
      intro i hi
      rcases ((HardinA233175PairStrip.good_iff s c).mp hc.2 i).2 hi with
        hh | ⟨r, _, hr⟩
      · exact hstate hh
      · exact htwo r hr
    have hb : ∀ x : Fin 6, beta x = 2 ↔ x = 2 ∨ x = 3 := by decide +kernel
    intro hx
    rcases (hb _).mp hx with hh | hh
    · exact htwo _ hh
    · exact hthree _ hh

private theorem initial_valid (c : Row)
    (hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c) :
    Valid (finish (false, false) c) (labels c) := by
  have hedge : (0 : Fin 6) ≠ c 1 ∧ (c 1).val ≠ 5 := by
    have hh := hc.2.1 (0 : Fin 5)
    change c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 5 at hh
    simpa only [hc.1, Fin.val_zero, zero_add] using hh
  have hcol : ∀ x : Fin 6, x ≠ 0 → x.val ≠ 5 → x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    decide +kernel
  have hone : ∃ i, c i = 1 := by
    rcases hcol _ (Ne.symm hedge.1) hedge.2 with hi | hi
    · exact ⟨1, hi⟩
    · rcases ((HardinA233175PairStrip.good_iff _ c).mp hc.2.2 1).1 hi with
        hh | ⟨i, _, hi⟩
      · cases hh
      · exact ⟨i, hi⟩
  exact valid_next _ c (Or.inr hone) ⟨hc.2.1, hc.2.2⟩

private theorem first_fibres (k : Fin 11) :
    firstCount k = ∑ q : Fin 5 → Fin 3, rowWeight (false, false) q *
      if (∀ j : Fin 5, (Fin.cons 0 q : Boundary) j.castSucc ≠
        (Fin.cons 0 q : Boundary) j.succ) ∧
        boundaryClass (rowFinish (false, false) q) (Fin.cons 0 q) = k then 1 else 0 := by
  unfold firstCount
  rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 6)).sum_comp, Fintype.sum_prod_type]
  change (∑ x : Fin 6, ∑ c : Fin 5 → Fin 6,
    if x = 0 ∧ rowLegal (Fin.cons x c) ∧ good (false, false) (Fin.cons x c) ∧
      boundaryClass (finish (false, false) (Fin.cons x c)) (labels (Fin.cons x c)) = k
      then (1 : ℤ) else 0) = _
  rw [Finset.sum_eq_single (0 : Fin 6)]
  · have hh := scanner_fibres 5 (false, false) (fun t q =>
      if (∀ j : Fin 5, (Fin.cons 0 q : Boundary) j.castSucc ≠
        (Fin.cons 0 q : Boundary) j.succ) ∧ boundaryClass t (Fin.cons 0 q) = k
        then (1 : ℤ) else 0)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro c _
    have hb : labels (Fin.cons 0 c) = Fin.cons 0 (fun j => beta (c j)) :=
      Fin.comp_cons beta 0 c
    have hg : good (false, false) (Fin.cons 0 c) ↔ good (false, false) c := by
      change (HardinA233175PairStrip.allowed (false, false) 0 ∧
        good (HardinA233175PairStrip.advance (false, false) 0) c) ↔ _
      simp only [show HardinA233175PairStrip.allowed (false, false) (0 : Fin 6) from
        by decide +kernel, show HardinA233175PairStrip.advance (false, false) (0 : Fin 6) =
          (false, false) from by decide +kernel, true_and]
    have hf : finish (false, false) (Fin.cons 0 c) = finish (false, false) c := rfl
    have hr : (∀ j : Fin 5,
        (Fin.cons 0 (fun i => beta (c i)) : Boundary) j.castSucc ≠
        (Fin.cons 0 (fun i => beta (c i)) : Boundary) j.succ) ↔
        rowLegal (Fin.cons 0 c) := by
      rw [← hb]
      simp only [labels, ← colour_bond_iff]
      rfl
    have hr' : (∀ j : Fin 5, labels (Fin.cons 0 c) j.castSucc ≠
        labels (Fin.cons 0 c) j.succ) ↔ rowLegal (Fin.cons 0 c) := by
      simpa only [hb] using hr
    simp only [eq_self, true_and, ← hb, hg, hf, hr']
    by_cases hc : good (false, false) c <;>
      simp only [hc, ↓reduceIte, true_and, and_false, false_and]
  · intro x _ hx
    simp [hx]
  · simp

private theorem initial_counts : ∀ k,
    firstCount k = ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k := by
  simp only [first_fibres]
  simp_rw [← (Fin.consEquiv (fun _ : Fin 5 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin 3)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv]
  decide +kernel

/-- The exact single-row transitions and first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 11 → ℤ
  | 0, _ => 1
  | n + 1, i => ∑ k : Fin 11, transfer i k * w n k

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (labels c) else 0) =
        ∑ k : Fin 11, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) * w n k := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s c (Or.inl h.1) ⟨hc.1, hc.2.2⟩)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k : Fin 11, classCount s p k * w n k) = _
    simp_rw [finite_certificate.1 s p h]
    rfl

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = ∑ k : Fin 11, ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k * w n k := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labels c) else 0) =
      ∑ k : Fin 11, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labels c) = k then (1 : ℤ) else 0) *
          w n k := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ k : Fin 11, firstCount k * w n k) = _
  simp_rw [finite_certificate.2]

private def distribution (r : Fin 9) (k : Fin 11) : ℤ :=
  ![![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8],
    ![1024, 10240, 18432, 14336, 19456, 17408, 11264, 8192, 3584, 13312, 7680],
    ![65536, 11894784, 19922944, 13697024, 20905984, 19136512, 9764864, 8257536, 2588672,
      13697024, 7602176],
    ![4194304, 12731809792, 21126709248, 13820231680, 22066233344, 20451426304, 9479127040,
      8522825728, 2319450112, 14390657024, 7769948160],
    ![268435456, 13439489540096, 22250346512384, 14285598097408, 23194970882048, 21600464273408,
      9656697094144, 8888569036800, 2285325254656, 15121506107392, 8067827630080],
    ![17179869184, 14129523280838656, 23375634386386944, 14905288863776768, 24350368624279552,
      22716013309067264, 10021859508617216, 9305227035410432, 2341169493180416,
      15875504796073984, 8431184010805248],
    ![1099511627776, 14834548759546822656, 24535730616681889792, 15605868810815406080,
      25552052095188729856, 23852115859181928448, 10472500808892022784, 9754613724198469632,
      2434602967651844096, 16659661645596852224, 8832477511238549504],
    ![70368744177664, 15567108237574814040064, 25744991932724816117760, 16360109272758489186304,
      26808812111241439870976, 25031000536475729133568, 10970884659964933046272,
      10230667782738877087744, 2545923396239978659840, 17479390576998738821120,
      9261247309720961679360],
    ![4503599627370496, 16332950328716430292287488, 27010652418350597978193920,
      17158719867507552292962304, 28125783903232205206323200, 26262820350752900696244224,
      11503471623921690059210752, 10731832335239811082223616, 2667781634235157838823424,
      18338196923878383063924736, 9714047525398103845765120]] r k

private theorem distribution_step : ∀ (r : Fin 8) (k : Fin 11),
    distribution r.succ k = ∑ i : Fin 11, distribution r.castSucc i * transfer i k := by
  decide +kernel

private theorem shifted_count (r : Fin 9) (n : ℕ) :
    (a (n + r.val + 1) : ℤ) = ∑ k : Fin 11, distribution r k * w n k := by
  induction r using Fin.induction generalizing n with
  | zero => exact a_eq_w n
  | succ r ih =>
    rw [show n + r.succ.val + 1 = (n + 1) + r.castSucc.val + 1 by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega, ih]
    simp only [w, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← distribution_step]

private theorem distribution_relation : ∀ k : Fin 11,
    distribution 8 k = 1984 * distribution 7 k -
      1314816 * distribution 6 k +
      411303936 * distribution 5 k -
      70111985664 * distribution 4 k +
      6893422510080 * distribution 3 k -
      389708152569856 * distribution 2 k +
      11733988091625472 * distribution 1 k -
      145241087982698496 * distribution 0 k := by
  decide +kernel

/-- Hardin's recurrence at every height at least nine, with the index shift explicit. -/
theorem result (n : ℕ) :
    (a (n + 9) : ℤ) = 1984 * a (n + 8) - 1314816 * a (n + 7) +
      411303936 * a (n + 6) - 70111985664 * a (n + 5) +
      6893422510080 * a (n + 4) - 389708152569856 * a (n + 3) +
      11733988091625472 * a (n + 2) - 145241087982698496 * a (n + 1) := by
  have h0 := shifted_count (0 : Fin 9) n
  have h1 := shifted_count (1 : Fin 9) n
  have h2 := shifted_count (2 : Fin 9) n
  have h3 := shifted_count (3 : Fin 9) n
  have h4 := shifted_count (4 : Fin 9) n
  have h5 := shifted_count (5 : Fin 9) n
  have h6 := shifted_count (6 : Fin 9) n
  have h7 := shifted_count (7 : Fin 9) n
  have h8 := shifted_count (8 : Fin 9) n
  change (a (n + 1) : ℤ) = _ at h0
  change (a (n + 2) : ℤ) = _ at h1
  change (a (n + 3) : ℤ) = _ at h2
  change (a (n + 4) : ℤ) = _ at h3
  change (a (n + 5) : ℤ) = _ at h4
  change (a (n + 6) : ℤ) = _ at h5
  change (a (n + 7) : ℤ) = _ at h6
  change (a (n + 8) : ℤ) = _ at h7
  change (a (n + 9) : ℤ) = _ at h8
  rw [h8, h7, h6, h5, h4, h3, h2, h1, h0]
  simp_rw [distribution_relation, sub_mul, add_mul]
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, Finset.mul_sum]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
