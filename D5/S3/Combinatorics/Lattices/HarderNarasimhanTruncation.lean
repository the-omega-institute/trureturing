/- GID: D5/S3/Combinatorics/Lattices/HarderNarasimhanTruncation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/HarderNarasimhanTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical slope thresholds cut HN chains with quantitative rank loss. -/

import D5.S3.Combinatorics.Lattices.HarderNarasimhan
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Threshold truncations of finite Harder--Narasimhan chains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation

open D5.S3.Combinatorics.Lattices.HarderNarasimhan

universe u
variable {Λ : Type u} [Lattice Λ]

/-- The HN slope multiset, with each factor slope repeated according to its rank. -/
def slopeList (D : SlopeData Λ) (a : Λ) : List Λ → List ℝ
  | [] => []
  | e :: l => List.replicate (D.rank e - D.rank a).toNat (D.slope a e) ++
      slopeList D e l

private theorem factor_rank_cast (D : SlopeData Λ) {a e : Λ} (h : a ≤ e) :
    (((D.rank e - D.rank a).toNat : ℕ) : ℝ) = (D.rank e : ℝ) - D.rank a := by
  have hz : ((D.rank e - D.rank a).toNat : ℤ) = D.rank e - D.rank a :=
    Int.natCast_toNat_eq_self.mpr (sub_nonneg.mpr (D.rank_strictMono.monotone h))
  exact_mod_cast hz

private theorem spectrum_length (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) :
    ((slopeList D a l).length : ℝ) = (D.rank b : ℝ) - D.rank a := by
  induction hf with
  | nil a => simp [slopeList]
  | @cons a e b l hs heb tail drop ih =>
    simp only [slopeList, List.length_append, List.length_replicate, Nat.cast_add,
      factor_rank_cast D hs.1.le, ih]
    ring

private theorem spectrum_sum (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) :
    (slopeList D a l).sum = D.degree b - D.degree a := by
  induction hf with
  | nil a => simp [slopeList]
  | @cons a e b l hs heb tail drop ih =>
    have hr : 0 < (D.rank e : ℝ) - D.rank a := by
      exact_mod_cast sub_pos.mpr (D.rank_strictMono hs.1)
    have hid : ((D.rank e : ℝ) - D.rank a) * D.slope a e =
        D.degree e - D.degree a := by
      dsimp [SlopeData.slope]
      field_simp [ne_of_gt hr]
    simp only [slopeList, List.sum_append, List.sum_replicate, nsmul_eq_mul,
      factor_rank_cast D hs.1.le, ih]
    linarith

private theorem spectrum_append (D : SlopeData Λ) {a c : Λ} {p : List Λ}
    (hp : D.Filtration a c p) (q : List Λ) :
    slopeList D a (p ++ q) = slopeList D a p ++ slopeList D c q := by
  induction hp with
  | nil a => rfl
  | @cons a e c p hs heb tail drop ih =>
    simpa only [List.cons_append, slopeList, List.append_assoc] using
      congrArg (fun l => List.replicate (D.rank e - D.rank a).toNat (D.slope a e) ++ l) ih

private def above (D : SlopeData Λ) (a : Λ) (t : ℝ) : List Λ → Prop
  | [] => True
  | e :: l => t ≤ D.slope a e ∧ above D e t l

private theorem startsBelow_prefix (D : SlopeData Λ) (a : Λ) (t : ℝ)
    (p q : List Λ) (h : D.StartsBelow a t (p ++ q)) : D.StartsBelow a t p := by
  cases p <;> simp_all [SlopeData.StartsBelow]

private theorem cut_chain (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) (t : ℝ) :
    ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c p ∧ D.Filtration c b q ∧
      above D a t p ∧ D.StartsBelow c t q ∧ l = p ++ q := by
  induction hf with
  | nil a => exact ⟨a, [], [], le_rfl, le_rfl, .nil a, .nil a, trivial, trivial, rfl⟩
  | @cons a e b l hs heb tail drop ih =>
    by_cases ht : t ≤ D.slope a e
    · obtain ⟨c, p, q, hec, hcb, hp, hq, hpa, hqb, hl⟩ := ih
      refine ⟨c, e :: p, q, hs.1.le.trans hec, hcb, ?_, hq, ⟨ht, hpa⟩, hqb, ?_⟩
      · exact .cons hs hec hp (startsBelow_prefix D e (D.slope a e) p q (hl ▸ drop))
      · simp [hl]
    · exact ⟨a, [], e :: l, le_rfl, hs.1.le.trans heb, .nil a,
        .cons hs heb tail drop, trivial, lt_of_not_ge ht, rfl⟩

private theorem above_last (D : SlopeData Λ) {a b e : Λ} {l : List Λ}
    (hf : D.Filtration a b (e :: l)) {t : ℝ} (ha : above D a t (e :: l)) :
    t ≤ D.slope (lastLower a (e :: l)) b := by
  cases l with
  | nil =>
    cases hf with
    | cons hs heb tail drop =>
      cases tail
      exact ha.1
  | cons f l =>
    cases hf with
    | cons hs heb tail drop => exact above_last D tail ha.2
termination_by l.length

private theorem above_spectrum (D : SlopeData Λ) {a : Λ} {t : ℝ} {l : List Λ}
    (ha : above D a t l) : ∀ x ∈ slopeList D a l, t ≤ x := by
  induction l generalizing a with
  | nil => simp [slopeList]
  | cons e l ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx' := List.eq_of_mem_replicate hx
      simpa only [hx'] using ha.1
    · exact ih ha.2 x hx

private theorem below_spectrum (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) {t : ℝ} (ht : D.StartsBelow a t l) :
    ∀ x ∈ slopeList D a l, x < t := by
  induction hf with
  | nil a => simp [slopeList]
  | @cons a e b l hs heb tail drop ih =>
    intro x hx
    have hfirst : D.slope a e < t := ht
    rcases List.mem_append.mp hx with hx | hx
    · have hx' := List.eq_of_mem_replicate hx
      simpa only [hx'] using hfirst
    · have htail : D.StartsBelow e t l := by
        cases l with
        | nil => trivial
        | cons f l => exact drop.trans hfirst
      exact ih htail x hx

private theorem all_above_last (D : SlopeData Λ) {a b e : Λ} {l : List Λ}
    (hf : D.Filtration a b (e :: l)) :
    above D a (D.slope (lastLower a (e :: l)) b) (e :: l) := by
  cases l with
  | nil =>
    cases hf with
    | cons hs heb tail drop =>
      cases tail
      exact ⟨le_rfl, trivial⟩
  | cons f l =>
    cases hf with
    | cons hs heb tail drop =>
      have ih := all_above_last D tail
      exact ⟨ih.1.trans drop.le, ih⟩
termination_by l.length

private theorem spectrum_extremes (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) :
    ∀ x ∈ slopeList D a l, D.muMin a b ≤ x ∧ x ≤ D.muMax a b := by
  cases l with
  | nil => simp [slopeList]
  | cons e l =>
    have he := filtration_extremes D a b e l hf
    intro x hx
    constructor
    · rw [he.2.2.2.2.2.1]
      exact above_spectrum D (all_above_last D hf) x hx
    · rw [he.2.2.2.2.1]
      rcases List.mem_append.mp hx with hx | hx
      · exact (List.eq_of_mem_replicate hx).le
      · cases hf with
        | cons hs heb tail drop => exact (below_spectrum D tail drop x hx).le

private theorem cut_count (D : SlopeData Λ) {a b c : Λ} {p q : List Λ} {t : ℝ}
    (hp : D.Filtration a c p) (hq : D.Filtration c b q)
    (hpa : above D a t p) (hqb : D.StartsBelow c t q) :
    (((slopeList D a (p ++ q)).filter (fun x => decide (x < t))).length : ℝ) =
      (D.rank b : ℝ) - D.rank c := by
  have hpf : (slopeList D a p).filter (fun x => decide (x < t)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simpa using not_lt.mpr (above_spectrum D hpa x hx)
  have hqf : (slopeList D c q).filter (fun x => decide (x < t)) = slopeList D c q := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true (below_spectrum D hq hqb x hx)
  rw [spectrum_append D hp q, List.filter_append, hpf, hqf, List.nil_append]
  exact spectrum_length D hq

/-- A slope threshold cuts an HN chain into a high-slope prefix and a low-slope suffix.
The returned chains concatenate to the original endpoint chain. -/
theorem threshold_truncation (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) (t : ℝ) :
    ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c p ∧ D.Filtration c b q ∧
      l = p ++ q ∧ (a < c → t ≤ D.muMin a c) ∧
      (c < b → D.muMax c b < t) ∧
      (((slopeList D a l).filter (fun x => decide (x < t))).length : ℝ) =
        (D.rank b : ℝ) - D.rank c := by
  obtain ⟨c, p, q, hac, hcb, hp, hq, hpa, hqb, hl⟩ := cut_chain D hf t
  refine ⟨c, p, q, hac, hcb, hp, hq, hl, ?_, ?_, ?_⟩
  · intro hlt
    cases p with
    | nil => cases hp; exact (lt_irrefl _ hlt).elim
    | cons e p =>
      have he := filtration_extremes D a c e p hp
      rw [he.2.2.2.2.2.1]
      exact above_last D hp hpa
  · intro hlt
    cases q with
    | nil => cases hq; exact (lt_irrefl _ hlt).elim
    | cons e q =>
      have he := filtration_extremes D c b e q hq
      rw [he.2.2.2.2.1]
      exact hqb
  · rw [hl]
    exact cut_count D hp hq hpa hqb

private theorem degree_le_max (D : SlopeData Λ) {a b c : Λ}
    (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    D.degree c - D.degree a ≤ D.muMax a b * ((D.rank c : ℝ) - D.rank a) := by
  rcases eq_or_lt_of_le hac with rfl | hac
  · simp
  · obtain ⟨l, hf, _⟩ := (exists_unique_filtration D a b).mpr hab.le
    cases l with
    | nil => cases hf; exact (lt_irrefl _ hab).elim
    | cons e l =>
      have he := filtration_extremes D a b e l hf
      have hb : D.slope a c ≤ D.muMax a b := by
        rw [he.2.2.2.2.1]
        exact he.2.2.1.2 ⟨c, hac, hcb, rfl⟩
      have hr : 0 < (D.rank c : ℝ) - D.rank a := by
        exact_mod_cast sub_pos.mpr (D.rank_strictMono hac)
      exact (div_le_iff₀ hr).mp hb

private theorem degree_le_threshold (D : SlopeData Λ) {a b : Λ}
    (hab : a ≤ b) {t : ℝ} (ht : a < b → D.muMax a b < t) :
    D.degree b - D.degree a ≤ t * ((D.rank b : ℝ) - D.rank a) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  · have h := degree_le_max D hab hab.le le_rfl
    have hr : 0 ≤ (D.rank b : ℝ) - D.rank a := by
      exact_mod_cast sub_nonneg.mpr (D.rank_strictMono.monotone hab.le)
    exact h.trans (mul_le_mul_of_nonneg_right (ht hab).le hr)

/-- The low-slope rank is bounded by the exact mean/maximal-slope deficit.
The undivided inequality adds across independent source objects. -/
theorem quantitative_truncation (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) (s u τ : ℝ)
    (hmax : a < b → D.muMax a b ≤ s + u) :
    ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c p ∧ D.Filtration c b q ∧
      l = p ++ q ∧ (a < c → s - τ ≤ D.muMin a c) ∧
      (c < b → D.muMax c b < s - τ) ∧
      (u + τ) * ((D.rank b : ℝ) - D.rank c) ≤
        (s + u) * ((D.rank b : ℝ) - D.rank a) - (D.degree b - D.degree a) ∧
      (0 < u + τ →
        s * ((D.rank b : ℝ) - D.rank a) ≤ D.degree b - D.degree a →
        (D.rank b : ℝ) - D.rank c ≤
          u / (u + τ) * ((D.rank b : ℝ) - D.rank a)) ∧
      (c < b → (u + τ) * ((D.rank b : ℝ) - D.rank c) <
        (s + u) * ((D.rank b : ℝ) - D.rank a) - (D.degree b - D.degree a)) ∧
      (c < b → 0 < u + τ →
        s * ((D.rank b : ℝ) - D.rank a) ≤ D.degree b - D.degree a →
        (D.rank b : ℝ) - D.rank c <
          u / (u + τ) * ((D.rank b : ℝ) - D.rank a)) ∧
      (((slopeList D a l).filter (fun x => decide (x < s - τ))).length : ℝ) =
        (D.rank b : ℝ) - D.rank c := by
  obtain ⟨c, p, q, hac, hcb, hp, hq, hl, hmin, hlow, hcount⟩ :=
    threshold_truncation D hf (s - τ)
  have hab : a ≤ b := hac.trans hcb
  have hpre : D.degree c - D.degree a ≤
      (s + u) * ((D.rank c : ℝ) - D.rank a) := by
    rcases eq_or_lt_of_le hab with rfl | hab
    · have hc : c = a := le_antisymm hcb hac
      simp [hc]
    · exact (degree_le_max D hab hac hcb).trans
        (mul_le_mul_of_nonneg_right (hmax hab) (by
          exact_mod_cast sub_nonneg.mpr (D.rank_strictMono.monotone hac)))
  have hpost := degree_le_threshold D hcb hlow
  have hstrict (hcb' : c < b) : (u + τ) * ((D.rank b : ℝ) - D.rank c) <
      (s + u) * ((D.rank b : ℝ) - D.rank a) - (D.degree b - D.degree a) := by
    have hr : 0 < (D.rank b : ℝ) - D.rank c := by
      exact_mod_cast sub_pos.mpr (D.rank_strictMono hcb')
    have htail := (degree_le_max D hcb' hcb'.le le_rfl).trans_lt
      (mul_lt_mul_of_pos_right (hlow hcb') hr)
    nlinarith
  refine ⟨c, p, q, hac, hcb, hp, hq, hl, hmin, hlow, ?_, ?_, hstrict, ?_, hcount⟩
  · nlinarith
  · intro hden hmean
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  · intro hcb' hden hmean
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hden).mpr
    nlinarith [hstrict hcb']

/-- The finite HN slope multiset has the exact total rank and degree. Its strict lower
level count is exactly the rank of the low-slope quotient at the same threshold. -/
theorem hn_spectrum (D : SlopeData Λ) {a b : Λ} {l : List Λ}
    (hf : D.Filtration a b l) :
    ((slopeList D a l).length : ℝ) = (D.rank b : ℝ) - D.rank a ∧
      (slopeList D a l).sum = D.degree b - D.degree a ∧
      (∀ x ∈ slopeList D a l, D.muMin a b ≤ x ∧ x ≤ D.muMax a b) ∧
      ∀ t, ∃ c p q, a ≤ c ∧ c ≤ b ∧ D.Filtration a c p ∧ D.Filtration c b q ∧
        l = p ++ q ∧ (a < c → t ≤ D.muMin a c) ∧
        (c < b → D.muMax c b < t) ∧
        (((slopeList D a l).filter (fun x => decide (x < t))).length : ℝ) =
          (D.rank b : ℝ) - D.rank c := by
  refine ⟨spectrum_length D hf, spectrum_sum D hf, spectrum_extremes D hf, ?_⟩
  intro t
  exact threshold_truncation D hf t

end D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation

namespace D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
open scoped InnerProductSpace
open Module Finset LinearMap MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
/-- Squared Hilbert--Schmidt norm. -/
def hs2 (A : E →ₗ[ℝ] F) : ℝ := LinearMap.trace ℝ E (A.adjoint ∘ₗ A)
lemma scalar_rank_estimate (D R w e η ρ t X z : ℝ)
    (hD : 0 < D) (hR : 0 < R) (hwD : w ≤ D) (hρ : 0 ≤ ρ)
    (ht : R * (1 - Real.sqrt e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D)
    (hlow : t / D * w - Real.sqrt w * Real.sqrt X ≤ z)
    (hup : z ≤ R * (ρ + Real.sqrt (ρ * e))) (he4 : e ≤ 1 / 4) :
    w ≤ (η + 4 * ρ + 4 * Real.sqrt e) * D := by
  let s := Real.sqrt e
  let β := ρ + Real.sqrt (ρ * e)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg e
  have hs1 : s < 1 := by
    dsimp [s]
    apply lt_of_le_of_lt (Real.sqrt_le_sqrt he4)
    norm_num
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have ht0 : 0 < t := lt_of_lt_of_le (mul_pos hR (sub_pos.mpr hs1)) ht
  have hη : 0 ≤ η := by
    have hp : 0 ≤ η * t ^ 2 := by
      simpa only [zero_mul] using (le_div_iff₀ hD).mp (hX0.trans hX)
    exact nonneg_of_mul_nonneg_left hp (sq_pos_of_pos ht0)
  by_cases hw : 0 ≤ w
  swap
  · exact (le_of_not_ge hw).trans (by positivity)
  let y := D / t * Real.sqrt X
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy2 : y ^ 2 ≤ η * D := by
    have hXD : X * D ≤ η * t ^ 2 := (le_div_iff₀ hD).mp hX
    dsimp [y]
    rw [mul_pow, div_pow, Real.sq_sqrt hX0]
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos ht0)]
    nlinarith [mul_le_mul_of_nonneg_left hXD hD.le]
  have hyb : y ≤ Real.sqrt (η * D) := Real.le_sqrt_of_sq_le hy2
  have hty : t * y = D * Real.sqrt X := by dsimp [y]; field_simp
  have htd : D * (t / D) = t := by field_simp
  have h1 : t * (w - Real.sqrt w * y) ≤ D * R * β := by
    have h := mul_le_mul_of_nonneg_left (hlow.trans hup) hD.le
    calc
      _ = D * (t / D * w - Real.sqrt w * Real.sqrt X) := by
        calc
          _ = t * w - Real.sqrt w * (t * y) := by ring
          _ = D * (t / D * w - Real.sqrt w * Real.sqrt X) := by
            rw [hty]
            field_simp
            <;> ring
      _ ≤ D * R * β := by convert h using 1 <;> ring
  have h2 : R * β ≤ t * (β / (1 - s)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sub_pos.mpr hs1)).mpr
    convert mul_le_mul_of_nonneg_right ht hβ using 1 <;> ring
  have hmain : w - Real.sqrt (η * D) * Real.sqrt w ≤ D * (β / (1 - s)) := by
    have h3 := mul_le_mul_of_nonneg_left h2 hD.le
    have h4 := mul_le_mul_of_nonneg_left hyb (Real.sqrt_nonneg w)
    have h5 := mul_le_mul_of_nonneg_left h4 ht0.le
    apply le_of_mul_le_mul_left _ ht0
    nlinarith
  by_cases hρ1 : 1 ≤ ρ
  · have hlarge : 1 ≤ η + 4 * ρ + 4 * Real.sqrt e := by
      linarith [Real.sqrt_nonneg e]
    exact hwD.trans (by nlinarith)
  have hρe : Real.sqrt (ρ * e) ≤ Real.sqrt e := by
    by_cases he : 0 ≤ e
    · exact Real.sqrt_le_sqrt (by nlinarith)
    · rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hρ
        (le_of_not_ge he)), Real.sqrt_eq_zero_of_nonpos (le_of_not_ge he)]
  have hs2 : s ≤ 1 / 2 := by
    dsimp [s]
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by nlinarith⟩
  have hβ2 : β / (1 - s) ≤ 2 * β := by
    apply (div_le_iff₀ (sub_pos.mpr hs1)).mpr
    nlinarith
  have ham : Real.sqrt (η * D) * Real.sqrt w ≤ (η * D + w) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (η * D) - Real.sqrt w),
      Real.sq_sqrt (mul_nonneg hη hD.le), Real.sq_sqrt hw]
  have hDs := mul_le_mul_of_nonneg_left hβ2 hD.le
  dsimp [β] at hmain hDs
  nlinarith [mul_le_mul_of_nonneg_left hρe hD.le]

section Variance
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

private lemma variance_shift (Q : H →ₗ[ℝ] H) (hQ : Q.IsSymmetric) (t : ℝ) :
    hs2 (Q - (t : ℝ) • LinearMap.id) =
      (LinearMap.trace ℝ H (Q ∘ₗ Q)) -
        2 * t * (LinearMap.trace ℝ H Q) + t ^ 2 * finrank ℝ H := by
  have ha : (Q - (t : ℝ) • LinearMap.id).adjoint =
      Q - (t : ℝ) • LinearMap.id := by
    exact (hQ.sub (LinearMap.IsSymmetric.id.smul (by simp))).adjoint_eq
  rw [hs2, ha]
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp,
    LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id,
    map_sub, map_smul, LinearMap.trace_id]
  simp only [smul_eq_mul]
  ring

lemma variance_eq (Q : H →ₗ[ℝ] H) (hQ : Q.IsSymmetric) :
    hs2 (Q - (((LinearMap.trace ℝ H Q) / (finrank ℝ H : ℝ) : ℝ) : ℝ) •
      LinearMap.id) =
      (LinearMap.trace ℝ H (Q ∘ₗ Q)) -
        (LinearMap.trace ℝ H Q) ^ 2 / finrank ℝ H := by
  by_cases hD : finrank ℝ H = 0
  · letI : Subsingleton H := (Module.finrank_zero_iff (R := ℝ) (M := H)).mp hD
    have hQ0 : Q = 0 := Subsingleton.elim _ _
    simp [hQ0, hs2]
  rw [variance_shift Q hQ]
  have hd : (finrank ℝ H : ℝ) ≠ 0 := by exact_mod_cast hD
  field_simp
  <;> ring

end Variance

private lemma tail_antitone (c : ℝ) :
    Antitone (fun t : ℝ => if t < c then (1 : ℝ) else 0) := by
  intro a b hab
  by_cases hb : b < c
  · simp [hb, hab.trans_lt hb]
  · by_cases ha : a < c <;> simp [ha, hb]

private lemma tail_integral {c H : ℝ} (hc : 0 ≤ c) (hcH : c ≤ H) :
    (∫ t in (0 : ℝ)..H, if t < c then (1 : ℝ) else 0) = c := by
  have h₁ : IntervalIntegrable (fun t : ℝ => if t < c then (1 : ℝ) else 0)
      volume 0 c := (tail_antitone c).intervalIntegrable
  have h₂ : IntervalIntegrable (fun t : ℝ => if t < c then (1 : ℝ) else 0)
      volume c H := (tail_antitone c).intervalIntegrable
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by rw [ae_iff]; simp
  have e₁ : (∫ t in (0 : ℝ)..c, if t < c then (1 : ℝ) else 0) =
      ∫ _ in (0 : ℝ)..c, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with t ht hmem
    rw [Set.uIoc_of_le hc] at hmem
    simp [lt_of_le_of_ne hmem.2 ht]
  have e₂ : (∫ t in c..H, if t < c then (1 : ℝ) else 0) = 0 := by
    calc
      _ = ∫ _ in c..H, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall fun t ht => by
          rw [Set.uIoc_of_le hcH] at ht
          simp [not_lt.mpr ht.1.le]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂, e₁, e₂]
  simp

private lemma finite_deficit_bound {J : Type*} [Fintype J] (y : J → ℝ)
    (s H : ℝ) (w : ℝ → ℝ) (hH : 0 ≤ H) (hy : ∀ j, s - H ≤ y j)
    (hw : IntervalIntegrable w volume 0 H)
    (hcount : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter fun j => y j < s - t).card : ℝ) ≤ w t) :
    ∑ j, max (s - y j) 0 ≤ ∫ t in (0 : ℝ)..H, w t := by
  classical
  let g : J → ℝ → ℝ := fun j t => if t < s - y j then 1 else 0
  have hg (j : J) : IntervalIntegrable (g j) volume 0 H :=
    (tail_antitone (s - y j)).intervalIntegrable
  have hl (j : J) : max (s - y j) 0 ≤ ∫ t in (0 : ℝ)..H, g j t := by
    by_cases hj : 0 ≤ s - y j
    · rw [max_eq_left hj]
      exact (tail_integral hj (by linarith [hy j])).ge
    · rw [max_eq_right (le_of_not_ge hj)]
      exact intervalIntegral.integral_nonneg hH fun t _ => by
        dsimp [g]; split_ifs <;> norm_num
  have heq (t : ℝ) : ∑ j, g j t =
      ((univ.filter fun j => y j < s - t).card : ℝ) := by
    simp only [g]
    simp_rw [show ∀ j, (t < s - y j) ↔ y j < s - t by
      intro j; constructor <;> intro h <;> linarith]
    exact sum_boole _ _
  have hm := intervalIntegral.integral_mono_on hH
    (IntervalIntegrable.sum univ fun j _ => hg j) hw
      (fun t ht => by simp only [Finset.sum_apply]; rw [heq]; exact hcount t ht)
  simp only [Finset.sum_apply] at hm
  rw [intervalIntegral.integral_finsetSum (fun j _ => hg j)] at hm
  have hs := sum_le_sum fun j (_ : j ∈ univ) => hl j
  exact hs.trans hm

private lemma reciprocal_budget {u H : ℝ} (hu : 0 ≤ u) (hH : 0 ≤ H) :
    ContinuousOn (fun t : ℝ => u / (u + t)) (Set.uIcc 0 H) ∧
      (∫ t in (0 : ℝ)..H, u / (u + t)) = u * Real.log (1 + H / u) := by
  rcases hu.eq_or_lt with rfl | hu
  · exact ⟨by simpa using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.uIcc 0 H)), by simp⟩
  have hden : ∀ t ∈ Set.uIcc (0 : ℝ) H, u + t ≠ 0 := by
    rw [Set.uIcc_of_le hH]
    intro t ht
    linarith [ht.1]
  refine ⟨continuousOn_const.div (continuousOn_const.add continuousOn_id) hden, ?_⟩
  have hi := integral_inv_of_pos hu (by linarith : 0 < H + u)
  have ht : (∫ t in (0 : ℝ)..H, (u + t)⁻¹) = Real.log ((H + u) / u) := by
    simpa only [add_comm u, intervalIntegral.integral_comp_add_right, zero_add] using hi
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, ht]
  congr 2
  field_simp
  ring

/-- Integrating a reciprocal tail budget bounds positive deficits and the exact mean. -/
theorem finite_spectral_deficit {K : Type*} [Fintype K] (y : K → ℝ)
    (s u H e η D : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H)
    (hK : 0 < Fintype.card K) (hlow : ∀ j, s - H ≤ y j)
    (hcount : ∀ t ∈ Set.Icc (0 : ℝ) H,
      ((univ.filter fun j => y j < s - t).card : ℝ) ≤
        (η + 4 * (u / (u + t)) + 4 * Real.sqrt e) * D) :
    (∑ j, max (s - y j) 0) ≤
      D * (4 * u * Real.log (1 + H / u) + (η + 4 * Real.sqrt e) * H) ∧
    s - (∑ j, y j) / Fintype.card K ≤ D / Fintype.card K *
      (4 * u * Real.log (1 + H / u) + (η + 4 * Real.sqrt e) * H) := by
  classical
  let w : ℝ → ℝ := fun t => (η + 4 * (u / (u + t)) + 4 * Real.sqrt e) * D
  have hr := reciprocal_budget hu hH
  have hc : ContinuousOn w (Set.uIcc 0 H) :=
    ((continuousOn_const.add (continuousOn_const.mul hr.1)).add continuousOn_const).mul_const D
  have hint : (∫ t in (0 : ℝ)..H, w t) =
      D * (4 * u * Real.log (1 + H / u) + (η + 4 * Real.sqrt e) * H) := by
    dsimp [w]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_add
        (intervalIntegrable_const.add (hr.1.intervalIntegrable.const_mul 4))
        intervalIntegrable_const,
      intervalIntegral.integral_add intervalIntegrable_const
        (hr.1.intervalIntegrable.const_mul 4),
      intervalIntegral.integral_const_mul, hr.2,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  have hp := finite_deficit_bound y s H w hH hlow hc.intervalIntegrable hcount
  rw [hint] at hp
  refine ⟨hp, ?_⟩
  have hs : (Fintype.card K : ℝ) * s - ∑ j, y j ≤ ∑ j, max (s - y j) 0 := by
    have h := sum_le_sum fun j (_ : j ∈ univ) => le_max_left (s - y j) 0
    simpa only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] using h
  have hdim : (0 : ℝ) < Fintype.card K := by exact_mod_cast hK
  have hd := (div_le_div_of_nonneg_right (hs.trans hp) hdim.le)
  convert hd using 1 <;> field_simp <;> ring

end D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
