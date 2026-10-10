/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/SquarePrefixGeometry
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: SquarePrefixGeometry for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
line_restrict: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_right_col, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.middle_line
ends_restrict: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.middle_line
middle_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefixSquare_isASM
middle_line_sum: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefixSquare_isASM
mem_completeColumns: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_complete_column_range, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_shift_column_sum
completeColumns_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asm_prefix_zero_forbids_right_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asr_prefix_column_complete_before_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
prefix_first_column_zero: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
prefix_column_complete_at_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
prefix_one_column_bound: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound
prefix_outside_zero: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound
prefix_width: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
prefix_complete_column_range: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound
prefix_shift_column_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound
prefixSquare_isASM: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefixSquare_isASM
prefixSquare_avoids: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.extractColumnFibre
below_prefix_interior_not_minus: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus
below_prefix_interior_zero: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus
pivot_not_one_at_prefix_end: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus
pivot_no_minus_after_prefix: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound
first_column_zero_except_pivot: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
pivot_minus_only_at_end: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus
below_pivot_end_not_minus: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus
pivot_row_singleton_if_no_minus: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus
pivot_row_right_singleton: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset





lemma line_restrict {n m : ℕ} (a : Fin n → SignType) (b : Fin m → SignType)
    (f : Fin n → Fin m) (hf : StrictMono f) (hval : ∀ u, b (f u) = a u)
    (hout : ∀ x, (¬ ∃ u, f u = x) → b x = 0)
    (ha : Alternates b) (hs : StartsOne b) : Alternates a ∧ StartsOne a := by
  classical
  refine ⟨?_,?_⟩
  · intro u v huv hu hv hgap
    rw [←hval u] at hu
    rw [←hval v] at hv
    rw [←hval u,←hval v]
    apply ha (f u) (f v) (hf huv) hu hv
    intro x hux hxv
    by_cases hpre : ∃ w, f w = x
    · obtain ⟨w,rfl⟩ := hpre
      rw [hval]
      exact hgap w (hf.lt_iff_lt.mp hux) (hf.lt_iff_lt.mp hxv)
    · exact hout x hpre
  · intro u hu hgap
    rw [←hval u] at hu ⊢
    apply hs (f u) hu
    intro x hxu
    by_cases hpre : ∃ v, f v = x
    · obtain ⟨v,rfl⟩ := hpre
      rw [hval]
      exact hgap v (hf.lt_iff_lt.mp hxu)
    · exact hout x hpre

lemma ends_restrict {n m : ℕ} (a : Fin n → SignType) (b : Fin m → SignType)
    (f : Fin n → Fin m) (hf : StrictMono f) (hval : ∀ u, b (f u) = a u)
    (hout : ∀ x, (¬ ∃ u, f u = x) → b x = 0) (he : EndsOne b) : EndsOne a := by
  classical
  intro u hu hgap
  rw [←hval u] at hu ⊢
  apply he (f u) hu
  intro x hux
  by_cases hpre : ∃ v, f v = x
  · obtain ⟨v,rfl⟩ := hpre
    rw [hval]
    exact hgap v (hf.lt_iff_lt.mp hux)
  · exact hout x hpre



end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

def shiftCol {p k : ℕ} (hp : p+1 ≤ k) (x : Fin p) : Fin k :=
  Fin.castLE hp x.succ

private lemma middle_line {p k : ℕ} (hp : p+1 ≤ k) (a : Fin k → SignType)
    (ha : Alternates a) (hs : StartsOne a) (he : EndsOne a)
    (hout : ∀ c : Fin k, c.val = 0 ∨ p < c.val → a c = 0) :
    Alternates (fun x => a (shiftCol hp x)) ∧
      StartsOne (fun x => a (shiftCol hp x)) ∧ EndsOne (fun x => a (shiftCol hp x)) := by
  have hf : StrictMono (shiftCol hp) := (Fin.strictMono_castLE hp).comp Fin.strictMono_succ
  have hval (u : Fin p) : a (shiftCol hp u) = a (shiftCol hp u) := rfl
  have hz (c : Fin k) (hc : ¬ ∃ u, shiftCol hp u = c) : a c = 0 := by
    apply hout c
    by_cases h0 : c.val = 0
    · exact Or.inl h0
    · right
      by_contra hle
      have hu : c.val - 1 < p := by omega
      apply hc
      refine ⟨⟨c.val-1,hu⟩,?_⟩
      apply Fin.ext
      dsimp [shiftCol]
      omega
  exact ⟨(line_restrict _ a _ hf hval hz ha hs).1,
    (line_restrict _ a _ hf hval hz ha hs).2, ends_restrict _ a _ hf hval hz he⟩

private lemma middle_line_sum {p k : ℕ} (hp : p+1 ≤ k) (a : Fin k → SignType)
    (hout : ∀ c : Fin k, c.val = 0 ∨ p < c.val → a c = 0) :
    (∑ x : Fin p, (a (shiftCol hp x) : ℤ)) = ∑ c : Fin k, (a c : ℤ) := by
  have hf : StrictMono (shiftCol hp) := (Fin.strictMono_castLE hp).comp Fin.strictMono_succ
  have hz (c : Fin k) (hc : ¬ ∃ u, shiftCol hp u = c) : a c = 0 := by
    apply hout c
    by_cases h0 : c.val = 0
    · exact Or.inl h0
    · right
      by_contra hle
      have hu : c.val - 1 < p := by omega
      apply hc
      refine ⟨⟨c.val-1,hu⟩,?_⟩
      apply Fin.ext
      dsimp [shiftCol]
      omega
  exact sum_embed _ a _ hf (fun _ => rfl) hz

end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

private def completeColumns {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Finset (Fin k) := by
  classical
  exact univ.filter (fun c => colSum R c = 1)

private lemma mem_completeColumns {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (c : Fin k) :
    c ∈ completeColumns R ↔ colSum R c = 1 := by
  classical
  simp [completeColumns]

private lemma completeColumns_card {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : (completeColumns R).card = nonemptyRows R := by
  classical
  have hc : ((completeColumns R).card : ℤ) = ∑ c, colSum R c := by
    unfold completeColumns
    rw [natCast_card_filter]
    apply sum_congr rfl
    intro c _
    rcases asr_col_sum R hR c with h | h <;> simp [h]
  have ht := asr_total_sum R hR
  rw [sum_comm] at ht
  change (∑ c, colSum R c) = _ at ht
  omega

end
end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

private lemma asm_prefix_zero_forbids_right_one {m : ℕ} (M : Matrix (Fin m) (Fin m) SignType)
    (hM : IsASM M) (hav : ¬ Contains312 M) (i u : Fin m) (c b : Fin m)
    (hu : u < i) (hc : 0 < c.val) (hcb : c < b)
    (hfirst : M i ⟨0,by omega⟩ = 1) (hone : M u b = 1)
    (hzero : (∑ x : Fin i.val, (M (Fin.castLE (Nat.le_of_lt i.isLt) x) c : ℤ)) = 0) : False := by
  obtain ⟨v,hv,hvc⟩ := one_after_zero_prefix (Nat.le_of_lt i.isLt) (fun x => M x c) (hM.2.2 c) hzero
  by_cases hEq : v = i
  · subst v
    obtain ⟨a,h₀a,hac,ha⟩ := minus_between_ones (M i) (hM.1.1 i).1
      ⟨0,by omega⟩ c hc hfirst hvc
    obtain ⟨w,hiw,hw⟩ := one_after_minus_of_ends (fun x => M x a)
      (asm_column_ends_one hM a) i ha
    exact hav ⟨u,i,w,⟨0,by omega⟩,a,b,hu,hiw,h₀a,lt_trans hac hcb,hone,hfirst,hw⟩
  · have hiv : i < v := lt_of_le_of_ne hv (fun h => hEq h.symm)
    exact hav ⟨u,i,v,⟨0,by omega⟩,c,b,hu,hiv,hc,hcb,hone,hfirst,hvc⟩

private lemma asr_prefix_column_complete_before_one {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i u : Fin r) (c b : Fin k)
    (hu : u < i) (hc : 0 < c.val) (hcb : c < b)
    (hfirst : R i ⟨0,hk⟩ = 1) (hone : R u b = 1) :
    colSum (topRows R (Nat.le_of_lt i.isLt)) c = 1 := by
  rcases asr_col_sum (topRows R (Nat.le_of_lt i.isLt))
      (topRows_isASR R (Nat.le_of_lt i.isLt) hR) c with hz | honecol
  · obtain ⟨m,hr,hk',M,hM,hav,hcorner⟩ := he
    apply False.elim
    apply asm_prefix_zero_forbids_right_one M hM hav (Fin.castLE hr i) (Fin.castLE hr u)
      (Fin.castLE hk' c) (Fin.castLE hk' b) hu hc hcb
    · have hz : (⟨0,by omega⟩ : Fin m) = Fin.castLE hk' (⟨0,hk⟩ : Fin k) := by apply Fin.ext; rfl
      rw [hz,hcorner]
      exact hfirst
    · simpa only [hcorner] using hone
    · change (∑ x : Fin i.val, (M (Fin.castLE (Nat.le_of_lt (Fin.castLE hr i).isLt) x) (Fin.castLE hk' c) : ℤ)) = 0
      have hcast (x : Fin i.val) :
          Fin.castLE (Nat.le_of_lt (Fin.castLE hr i).isLt) x =
            Fin.castLE hr (Fin.castLE (Nat.le_of_lt i.isLt) x) := by apply Fin.ext; rfl
      simp only [hcast,hcorner]
      exact hz
  · exact honecol

end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

lemma prefix_first_column_zero {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hk : 0 < k) (i u : Fin r) (hu : u < i)
    (hfirst : R i ⟨0,hk⟩ = 1) : R u ⟨0,hk⟩ = 0 := by
  have hn := asr_first_col_not_minus R hR hk u
  have hnotone : R u ⟨0,hk⟩ ≠ 1 := by
    intro hone
    exact ne_of_lt hu (asr_first_col_one_unique R hR hk u i hone hfirst)
  cases h : R u ⟨0,hk⟩ <;> simp_all

private lemma prefix_column_complete_at_one {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i u : Fin r) (b : Fin k)
    (hu : u < i) (hfirst : R i ⟨0,hk⟩ = 1) (hone : R u b = 1) :
    colSum (topRows R (Nat.le_of_lt i.isLt)) b = 1 := by
  have hbpos : 0 < b.val := by
    by_contra h
    have hbzero : b = ⟨0,hk⟩ := by apply Fin.ext; change b.val = 0; omega
    have hz := prefix_first_column_zero R hR hk i u hu hfirst
    rw [← hbzero,hone] at hz
    exact (by decide : (1 : SignType) ≠ 0) hz
  let T := topRows R (Nat.le_of_lt i.isLt)
  have hT := topRows_isASR R (Nat.le_of_lt i.isLt) hR
  rcases asr_col_sum T hT b with hz | hs
  · rcases alternating_line_state (fun x => T x b) (hT.2 b).1 (hT.2 b).2 with
      ⟨hzero,_⟩ | ⟨x,hx,htail,_⟩
    · let up : Fin i.val := ⟨u.val,hu⟩
      have heq : Fin.castLE (Nat.le_of_lt i.isLt) up = u := by apply Fin.ext; rfl
      have hz' := hzero up
      change R (Fin.castLE (Nat.le_of_lt i.isLt) up) b = 0 at hz'
      rw [heq,hone] at hz'
      exact (by decide : (1 : SignType) ≠ 0) hz' |>.elim
    · have hminus := last_minus_of_zero_sum (fun x => T x b) (hT.2 b).1 (hT.2 b).2 hz x hx htail
      let v := Fin.castLE (Nat.le_of_lt i.isLt) x
      obtain ⟨c,hbc,hvc⟩ := one_after_minus_of_ends (R v) (hR.1 v).2.2 b hminus
      have hv : v < i := x.isLt
      have hdone := asr_prefix_column_complete_before_one R hR he hk i v b c hv hbpos hbc hfirst hvc
      change colSum T b = 1 at hdone
      omega
  · exact hs

private lemma prefix_one_column_bound {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i u : Fin r) (b : Fin k)
    (hu : u < i) (hfirst : R i ⟨0,hk⟩ = 1) (hone : R u b = 1)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) : b.val ≤ i.val := by
  classical
  let T := topRows R (Nat.le_of_lt i.isLt)
  have hbcomplete := prefix_column_complete_at_one R hR he hk i u b hu hfirst hone
  have hbcol (x : Fin b.val) :
      colSum T (⟨x.val+1,by have := x.isLt; have := b.isLt; omega⟩ : Fin k) = 1 := by
    let c : Fin k := ⟨x.val+1,by have := x.isLt; have := b.isLt; omega⟩
    change colSum T c = 1
    by_cases hEq : c = b
    · rw [hEq]
      exact hbcomplete
    · have hcb : c < b := by
        have hn : c.val ≠ b.val := fun h => hEq (Fin.ext h)
        have := x.isLt
        change x.val+1 < b.val
        dsimp [c] at hn
        omega
      exact asr_prefix_column_complete_before_one R hR he hk i u c b hu (by dsimp [c]; omega) hcb hfirst hone
  let f : Fin b.val ↪ completeColumns T :=
    { toFun := fun x => ⟨⟨x.val+1,by have := x.isLt; have := b.isLt; omega⟩,
        (mem_completeColumns T _).mpr (hbcol x)⟩
      inj' := by
        intro x y h
        apply Fin.ext
        have hv := congrArg (fun z : completeColumns T => z.val.val) h
        change x.val+1 = y.val+1 at hv
        omega }
  have hc := Nat.card_le_card_of_injective f f.injective
  have hn := topRows_nonemptyRows_of_before R (Nat.le_of_lt i.isLt) hbefore
  have hcard := completeColumns_card T (topRows_isASR R (Nat.le_of_lt i.isLt) hR)
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_fin] at hc
  change nonemptyRows T = i.val at hn
  omega

lemma prefix_outside_zero {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i u : Fin r) (b : Fin k)
    (hu : u < i) (hfirst : R i ⟨0,hk⟩ = 1) (hb : i.val < b.val)
    (hbefore : ∀ v : Fin r, v.val < i.val → ∃ c, R v c ≠ 0) : R u b = 0 := by
  have hn : R u b ≠ 1 := by
    intro hone
    exact not_lt_of_ge (prefix_one_column_bound R hR he hk i u b hu hfirst hone hbefore) hb
  have hm : R u b ≠ -1 := by
    intro hminus
    obtain ⟨v,hvu,hv⟩ := one_before_minus (fun x => R x b) (hR.2 b).2 u hminus
    exact not_lt_of_ge (prefix_one_column_bound R hR he hk i v b (lt_trans hvu hu) hfirst hv hbefore) hb
  cases h : R u b <;> simp_all

end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset
noncomputable section

lemma prefix_width {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hk : 0 < k) (i : Fin r) (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0) : i.val+1 ≤ k := by
  let T := topRows R (Nat.le_of_lt i.isLt)
  have hn := topRows_nonemptyRows_of_before R (Nat.le_of_lt i.isLt) hbefore
  have hb := deficientColumns_balance T (topRows_isASR R (Nat.le_of_lt i.isLt) hR)
  have hz : colSum T ⟨0,hk⟩ = 0 := by
    apply sum_eq_zero
    intro u _
    rw [show T u ⟨0,hk⟩ = 0 from prefix_first_column_zero R hR hk i
      (Fin.castLE (Nat.le_of_lt i.isLt) u) u.isLt hfirst]
    rfl
  have hm : (⟨0,hk⟩ : Fin k) ∈ deficientColumns T := (mem_deficientColumns T _).mpr hz
  have hc : 0 < (deficientColumns T).card := card_pos.mpr ⟨_,hm⟩
  change nonemptyRows T = i.val at hn
  omega

private lemma prefix_complete_column_range {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (c : completeColumns (topRows R (Nat.le_of_lt i.isLt))) :
    0 < c.val.val ∧ c.val.val ≤ i.val := by
  have hc := (mem_completeColumns _ c.val).mp c.property
  obtain ⟨u,_,hone⟩ := one_after_zero_prefix (show 0 ≤ i.val by omega)
    (fun u => topRows R (Nat.le_of_lt i.isLt) u c.val) hc (by simp)
  have hb : c.val.val ≤ i.val := prefix_one_column_bound R hR he hk i
    (Fin.castLE (Nat.le_of_lt i.isLt) u) c.val u.isLt hfirst hone hbefore
  refine ⟨?_,hb⟩
  by_contra h
  have hc0 : c.val = ⟨0,hk⟩ := by apply Fin.ext; change c.val.val = 0; omega
  rw [hc0] at hone
  have hz := prefix_first_column_zero R hR hk i (Fin.castLE (Nat.le_of_lt i.isLt) u) u.isLt hfirst
  exact (by decide : (1 : SignType) ≠ 0) (hone.symm.trans hz)

lemma prefix_shift_column_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (x : Fin i.val) :
    colSum (topRows R (Nat.le_of_lt i.isLt)) (shiftCol (prefix_width R hR hk i hfirst hbefore) x) = 1 := by
  let T := topRows R (Nat.le_of_lt i.isLt)
  let C := completeColumns T
  have hc : C.card = i.val := by
    rw [completeColumns_card T (topRows_isASR R (Nat.le_of_lt i.isLt) hR)]
    exact topRows_nonemptyRows_of_before R (Nat.le_of_lt i.isLt) hbefore
  let cAt := C.orderIsoOfFin hc
  have hrange (y : Fin i.val) : 0 < (cAt y).val.val ∧ (cAt y).val.val ≤ i.val :=
    prefix_complete_column_range R hR he hk i hfirst hbefore (cAt y)
  let f : Fin i.val → Fin i.val := fun y => ⟨(cAt y).val.val-1,by have := hrange y; omega⟩
  have hf : StrictMono f := by
    intro a b hab
    have hs := cAt.strictMono hab
    have ha := (hrange a).1
    have hb := (hrange b).1
    change (cAt a).val.val < (cAt b).val.val at hs
    change (cAt a).val.val-1 < (cAt b).val.val-1
    omega
  have heq := congrArg Fin.val (hf.apply_eq (x := x))
  change (cAt x).val.val-1 = x.val at heq
  have hcol : (cAt x).val = shiftCol (prefix_width R hR hk i hfirst hbefore) x := by
    apply Fin.ext
    change (cAt x).val.val = x.val+1
    have := (hrange x).1
    omega
  have hsum := (mem_completeColumns T (cAt x).val).mp (cAt x).property
  simpa only [hcol] using hsum

def prefixSquare {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (i : Fin r)
    (hp : i.val+1 ≤ k) : Matrix (Fin i.val) (Fin i.val) SignType :=
  fun u c => R (Fin.castLE (Nat.le_of_lt i.isLt) u) (shiftCol hp c)

lemma prefixSquare_isASM {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0) :
    IsASM (prefixSquare R i (prefix_width R hR hk i hfirst hbefore)) := by
  let hp := prefix_width R hR hk i hfirst hbefore
  have hout (u : Fin i.val) (c : Fin k) (hc : c.val=0 ∨ i.val < c.val) :
      R (Fin.castLE (Nat.le_of_lt i.isLt) u) c = 0 := by
    rcases hc with hc | hc
    · have heq : c = ⟨0,hk⟩ := Fin.ext hc
      rw [heq]
      exact prefix_first_column_zero R hR hk i _ u.isLt hfirst
    · exact prefix_outside_zero R hR he hk i _ c u.isLt hfirst hc hbefore
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro u
    exact middle_line hp _ (hR.1 _).1 (hR.1 _).2.1 (hR.1 _).2.2 (hout u)
  · intro c
    exact (prefix_line (Nat.le_of_lt i.isLt) (fun u => R u (shiftCol hp c))
      (hR.2 _).1 (hR.2 _).2)
  · intro u
    rw [show (∑ c, (prefixSquare R i hp u c : ℤ)) = ∑ c, (R (Fin.castLE (Nat.le_of_lt i.isLt) u) c : ℤ) from
      middle_line_sum hp _ (hout u)]
    apply (asr_row_sum_one_iff R hR _).mpr
    exact hbefore _ u.isLt
  · intro c
    exact prefix_shift_column_sum R hR he hk i hfirst hbefore c

end
end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

lemma prefixSquare_avoids {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) (i : Fin r) (hp : i.val+1 ≤ k) :
    ¬ Contains312 (prefixSquare R i hp) := by
  rintro ⟨u,v,w,a,b,c,hu,hv,ha,hb,h₁,h₂,h₃⟩
  apply extAvoids312_corner R he
  exact ⟨Fin.castLE (Nat.le_of_lt i.isLt) u, Fin.castLE (Nat.le_of_lt i.isLt) v,
    Fin.castLE (Nat.le_of_lt i.isLt) w,shiftCol hp a,shiftCol hp b,shiftCol hp c,
    hu,hv,by change a.val+1 < b.val+1; omega,
    by change b.val+1 < c.val+1; omega,h₁,h₂,h₃⟩

private lemma below_prefix_interior_not_minus {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i v : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (hv : i.val ≤ v.val) (c : Fin k) (hc : 0 < c.val) (hcp : c.val < i.val) :
    R v c ≠ -1 := by
  intro hminus
  have hp := prefix_width R hR hk i hfirst hbefore
  let p : Fin k := ⟨i.val,by omega⟩
  have hsum : colSum (topRows R (Nat.le_of_lt i.isLt)) p = 1 := by
    have hs := prefix_shift_column_sum R hR he hk i hfirst hbefore
      (⟨i.val-1,by omega⟩ : Fin i.val)
    have heq : shiftCol hp (⟨i.val-1,by omega⟩ : Fin i.val) = p := by
      apply Fin.ext
      change i.val-1+1=i.val
      omega
    simpa only [heq] using hs
  obtain ⟨u,_,hu⟩ := one_after_zero_prefix (show 0 ≤ i.val by omega)
    (fun u => topRows R (Nat.le_of_lt i.isLt) u p) hsum (by simp)
  obtain ⟨m,hr,hk',M,hM,hav,hcorner⟩ := he
  have hm : M (Fin.castLE hr v) (Fin.castLE hk' c) = -1 := by rw [hcorner]; exact hminus
  obtain ⟨w,hvw,hw⟩ := one_after_minus_of_ends (fun x => M x (Fin.castLE hk' c))
    (asm_column_ends_one hM _) (Fin.castLE hr v) hm
  apply hav
  refine ⟨Fin.castLE hr (Fin.castLE (Nat.le_of_lt i.isLt) u),Fin.castLE hr i,w,
    Fin.castLE hk' ⟨0,hk⟩,Fin.castLE hk' c,Fin.castLE hk' p,u.isLt,?_,hc,hcp,?_,?_,hw⟩
  · change i.val < w.val
    change v.val < w.val at hvw
    omega
  · rw [hcorner]
    exact hu
  · rw [hcorner]
    exact hfirst

lemma below_prefix_interior_zero {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i v : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (hv : i.val ≤ v.val) (c : Fin k) (hc : 0 < c.val) (hcp : c.val < i.val) :
    R v c = 0 := by
  have hp := prefix_width R hR hk i hfirst hbefore
  let T := topRows R (Nat.le_of_lt i.isLt)
  have hs : colSum T c = 1 := by
    have hsum := prefix_shift_column_sum R hR he hk i hfirst hbefore
      (⟨c.val-1,by omega⟩ : Fin i.val)
    have heq : shiftCol hp (⟨c.val-1,by omega⟩ : Fin i.val) = c := by
      apply Fin.ext
      change c.val-1+1=c.val
      omega
    simpa only [heq] using hsum
  change (∑ u, (T u c : ℤ)) = 1 at hs
  have hT := topRows_isASR R (Nat.le_of_lt i.isLt) hR
  rcases alternating_line_state (fun u => T u c) (hT.2 c).1 (hT.2 c).2 with ⟨hz,hzsum⟩ | ⟨u,hu,htail,huSum⟩
  · exact (by decide : (0 : ℤ) ≠ 1) (hzsum.symm.trans hs) |>.elim
  · have hone : T u c = 1 := by
      by_contra hn
      simp only [hn,if_false] at huSum
      omega
    have hnm := below_prefix_interior_not_minus R hR he hk i v hfirst hbefore hv c hc hcp
    by_contra hne
    have hvone : R v c = 1 := by cases hs : R v c <;> simp_all
    obtain ⟨z,huz,hzv,hzm⟩ := minus_between_ones (fun x => R x c) (hR.2 c).1
      (Fin.castLE (Nat.le_of_lt i.isLt) u) v (by change u.val < v.val; omega) hone hvone
    by_cases hz : z.val < i.val
    · have hzt := htail ⟨z.val,hz⟩ huz
      change R (Fin.castLE (Nat.le_of_lt i.isLt) ⟨z.val,hz⟩) c = 0 at hzt
      have heq : Fin.castLE (Nat.le_of_lt i.isLt) (⟨z.val,hz⟩ : Fin i.val) = z := by apply Fin.ext; rfl
      rw [heq,hzm] at hzt
      exact (by decide : (-1 : SignType) ≠ 0) hzt
    · exact below_prefix_interior_not_minus R hR he hk i z hfirst hbefore (by omega) c hc hcp hzm

lemma pivot_not_one_at_prefix_end {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (hi : 0 < i.val) : R i ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ ≠ 1 := by
  intro hone
  obtain ⟨c,hc,hcp,hcm⟩ := minus_between_ones (R i) (hR.1 i).1
    ⟨0,hk⟩ ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ hi hfirst hone
  exact below_prefix_interior_not_minus R hR he hk i i hfirst hbefore (le_refl _) c hc hcp hcm

lemma pivot_no_minus_after_prefix {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (c : Fin k) (hc : i.val < c.val) : R i c ≠ -1 := by
  intro hm
  obtain ⟨u,hu,hone⟩ := one_before_minus (fun x => R x c) (hR.2 c).2 i hm
  have hz := prefix_outside_zero R hR he hk i u c hu hfirst hc hbefore
  exact (by decide : (1 : SignType) ≠ 0) (hone.symm.trans hz)

end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
open Finset

lemma first_column_zero_except_pivot {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hk : 0 < k) (i : Fin r) (hfirst : R i ⟨0,hk⟩ = 1) :
    ∀ v, R v ⟨0,hk⟩ = if v = i then 1 else 0 :=
  line_no_minus_singleton _ (hR.2 _).1 (asr_first_col_not_minus R hR hk) i hfirst

private lemma pivot_minus_only_at_end {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (c : Fin k) (hm : R i c = -1) : c.val = i.val := by
  by_cases hc : c.val = 0
  · have heq : c = ⟨0,hk⟩ := Fin.ext hc
    exact (asr_first_col_not_minus R hR hk i (by simpa only [heq] using hm)).elim
  rcases lt_trichotomy c.val i.val with hlt | heq | hgt
  · exact (below_prefix_interior_not_minus R hR he hk i i hfirst hbefore
      (le_refl _) c (by omega) hlt hm).elim
  · exact heq
  · exact (pivot_no_minus_after_prefix R hR he hk i hfirst hbefore c hgt hm).elim

lemma below_pivot_end_not_minus {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i v : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (hi : 0 < i.val) (hv : i.val < v.val) :
    R v ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ ≠ -1 := by
  intro hm
  by_cases hmi : R i ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ = -1
  · have heq := asr_column_minus_unique R he
      ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ i v hmi hm
    have := congrArg Fin.val heq
    omega
  obtain ⟨c,hc,hone⟩ := one_before_minus (R v) (hR.1 v).2.1
    ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ hm
  by_cases hc0 : c.val=0
  · have heq : c=⟨0,hk⟩ := Fin.ext hc0
    have hz := first_column_zero_except_pivot R hR hk i hfirst v
    have hne : v ≠ i := by intro h; subst v; omega
    simp only [if_neg hne] at hz
    rw [heq,hz] at hone
    exact (by decide : (0 : SignType) ≠ 1) hone
  · have hz := below_prefix_interior_zero R hR he hk i v hfirst hbefore
      (le_of_lt hv) c (by omega) hc
    exact (by decide : (0 : SignType) ≠ 1) (hz.symm.trans hone)

lemma pivot_row_singleton_if_no_minus {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (hn : R i ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ ≠ -1) :
    ∀ c, R i c = if c.val=0 then 1 else 0 := by
  have hnm (c : Fin k) : R i c ≠ -1 := by
    intro hm
    have hc := pivot_minus_only_at_end R hR he hk i hfirst hbefore c hm
    have heq : c = ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ := Fin.ext hc
    exact hn (by simpa only [heq] using hm)
  have hs := line_no_minus_singleton (R i) (hR.1 i).1 hnm ⟨0,hk⟩ hfirst
  intro c
  simpa only [Fin.ext_iff] using hs c

lemma pivot_row_right_singleton {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hk : 0 < k) (i : Fin r)
    (hfirst : R i ⟨0,hk⟩ = 1)
    (hbefore : ∀ u : Fin r, u.val < i.val → ∃ c, R u c ≠ 0)
    (hm : R i ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ = -1) :
    ∃ q : Fin k, i.val < q.val ∧ ∀ c : Fin k, i.val < c.val →
      R i c = if c = q then 1 else 0 := by
  obtain ⟨q,hq,hqone⟩ := one_after_minus_of_ends (R i) (hR.1 i).2.2
    ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ hm
  refine ⟨q,hq,?_⟩
  intro c hc
  by_cases heq : c=q
  · simp [heq,hqone]
  · rw [if_neg heq]
    have hn := pivot_no_minus_after_prefix R hR he hk i hfirst hbefore c hc
    by_contra hne
    have hone : R i c = 1 := by cases hv : R i c <;> simp_all
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · obtain ⟨z,hcz,_,hzm⟩ := minus_between_ones (R i) (hR.1 i).1 c q hlt hone hqone
      have heq := asr_row_minus_unique R he i
        ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ z hm hzm
      have hval : i.val = z.val := congrArg Fin.val heq
      have hltz := lt_trans hc hcz
      omega
    · obtain ⟨z,hqz,_,hzm⟩ := minus_between_ones (R i) (hR.1 i).1 q c hgt hqone hone
      have heq := asr_row_minus_unique R he i
        ⟨i.val,by have := prefix_width R hR hk i hfirst hbefore; omega⟩ z hm hzm
      have hval : i.val = z.val := congrArg Fin.val heq
      have hltz := lt_trans hq hqz
      omega

end D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry
