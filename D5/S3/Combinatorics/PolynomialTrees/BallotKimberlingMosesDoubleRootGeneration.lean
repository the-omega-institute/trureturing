/- GID: D5/S3/Combinatorics/PolynomialTrees/BallotKimberlingMosesDoubleRootGeneration
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PolynomialTrees/BallotKimberlingMosesDoubleRootGeneration
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact double-root tree shells imply the Table 5 recurrence from index three. -/

/-
proof_shape: result: content; expansion uses seen_spec, an induction carrying exact reach bounds.
escape_witness: none; admission uses the external open-problem settlement.
admission_basis: open-problem-resolution (#23638; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24117
The public definitions retain the polynomial-remainder construction; the private pair model
is related to it by seen_spec.
Utility none: unbounded exact reachability, shell counting and recurrence; finite root facts
are consumed helpers rather than a positive finite-enumeration deliverable.
proof_shape: q_square: bind-only; consumers: q_monic, q_degree; escape_witness: none.
proof_shape: q_monic: bind-only; consumers: label_mod, mulChild_label; escape_witness: none.
proof_shape: q_degree: bind-only; consumers: label_degree; escape_witness: none.
proof_shape: label_degree: bind-only; consumers: label_mod; escape_witness: none.
proof_shape: label_mod: bind-only; consumers: addChild_label, mulChild_label; escape_witness: none.
proof_shape: label_zero: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: label_injective: bind-only; consumers: label_mem_seen, rowLabel_injective, top_not_in_rows; escape_witness: none.
proof_shape: addChild_label: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: mulChild_label: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: valid_mono: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: valid_add: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: valid_mul: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: valid_predecessor: bind-only; consumers: seen_spec; escape_witness: none.
proof_shape: seen_spec: content; consumers: label_mem_seen, generation_succ_spec; escape_witness: none.
proof_shape: label_mem_seen: content; consumers: generation_succ_spec; escape_witness: none.
proof_shape: generation_succ_spec: content; consumers: generation_succ_eq; escape_witness: none.
proof_shape: rowLabel_injective: bind-only; consumers: G_succ; escape_witness: none.
proof_shape: generation_succ_eq: content; consumers: G_succ; escape_witness: none.
proof_shape: top_not_in_rows: bind-only; consumers: G_succ; escape_witness: none.
proof_shape: G_succ: content; consumers: G_sum; escape_witness: none.
proof_shape: G_zero: bind-only; consumers: G_sum; escape_witness: none.
proof_shape: G_sum: content; consumers: G_difference; escape_witness: none.
proof_shape: G_difference: content; consumers: result; escape_witness: none.
-/

import Mathlib.Algebra.Polynomial.Div

/-! The polynomial-form tree for the double-root row of Table 5.
The pair coordinates are proved to describe the literal monic-remainder operations.
-/

namespace D5.S3.Combinatorics.PolynomialTrees.BallotKimberlingMosesDoubleRootGeneration

open Polynomial

noncomputable section

/-- The fixed polynomial from the selected Table 5 row. -/
def q : Polynomial ℤ := X ^ 2 - 2 * X + 1

/-- First child, reduced modulo the source's fixed monic polynomial. -/
def addChild (p : Polynomial ℤ) : Polynomial ℤ := (p + 1) %ₘ q

/-- Second child, reduced modulo the source's fixed monic polynomial. -/
def mulChild (p : Polynomial ℤ) : Polynomial ℤ := (X * p) %ₘ q

/-- All distinct labels reached by at most n source operations, including the root. -/
def seen : ℕ → Finset (Polynomial ℤ)
  | 0 => {0}
  | n + 1 => seen n ∪ (seen n).image addChild ∪ (seen n).image mulChild

/-- Generation zero is the root; later generations delete every earlier label. -/
def generation : ℕ → Finset (Polynomial ℤ)
  | 0 => {0}
  | n + 1 => seen (n + 1) \ seen n

/-- The source's generation-cardinality sequence G_n. -/
def G (n : ℕ) : ℕ := (generation n).card

/-- The complete eventual-recurrence assertion for the selected Table 5 row. -/
def claim : Prop :=
  ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (G n : ℤ) = 3 * (G (n - 1) : ℤ) - 3 * (G (n - 2) : ℤ) + (G (n - 3) : ℤ)

end

end D5.S3.Combinatorics.PolynomialTrees.BallotKimberlingMosesDoubleRootGeneration

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace D5.S3.Combinatorics.PolynomialTrees.BallotKimberlingMosesDoubleRootGeneration
open Polynomial
noncomputable section

private def label (a b : ℕ) : Polynomial ℤ := C (a : ℤ) + C (b : ℤ) * (X - 1)

private theorem q_square : q = (X - C (1 : ℤ)) ^ 2 := by
  simpa only [q, map_one, mul_one, one_pow] using (sub_sq (X : Polynomial ℤ) 1).symm

private theorem q_monic : q.Monic := by
  rw [q_square]
  exact (monic_X_sub_C (1 : ℤ)).pow 2

private theorem q_degree : q.degree = 2 := by
  rw [q_square, degree_pow, degree_X_sub_C]
  norm_num

private theorem label_degree (a b : ℕ) : (label a b).degree < q.degree := by
  rw [q_degree]
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact degree_C_le.trans_lt (by norm_num)
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le (by simpa only [map_one] using (degree_X_sub_C (1 : ℤ)).le)
      _ < (2 : WithBot ℕ) := by norm_num

private theorem label_mod (a b : ℕ) : label a b %ₘ q = label a b := by
  exact (modByMonic_eq_self_iff q_monic).mpr (label_degree a b)

private theorem label_zero : label 0 0 = 0 := by simp [label]

private theorem label_injective : Function.Injective (fun t : ℕ × ℕ => label t.1 t.2) := by
  intro ⟨a,b⟩ ⟨c,d⟩ h
  have hb : (b : ℤ) = d := by
    have hh := congrArg (fun p : Polynomial ℤ => p.coeff 1) h
    simpa [label, coeff_add, coeff_C_mul, coeff_sub, coeff_one, coeff_X] using hh
  have ha : (a : ℤ) = c := by
    have hh := congrArg (fun p : Polynomial ℤ => p.eval 1) h
    simpa [label] using hh
  exact Prod.ext (by exact_mod_cast ha) (by exact_mod_cast hb)

private theorem addChild_label (a b : ℕ) : addChild (label a b) = label (a+1) b := by
  unfold addChild
  have h : label a b + 1 = label (a+1) b := by simp [label, Nat.cast_add, map_add]; ring
  rw [h, label_mod]

private theorem mulChild_label (a b : ℕ) : mulChild (label a b) = label a (b+a) := by
  unfold mulChild
  calc
    (X * label a b) %ₘ q = label a (b+a) %ₘ q := by
      apply modByMonic_eq_of_dvd_sub q_monic
      refine ⟨C (b : ℤ), ?_⟩
      simp [label, q, Nat.cast_add, map_add]
      ring
    _ = _ := label_mod _ _



private def valid (n a b : ℕ) : Prop :=
  (a = 0 ∧ b = 0) ∨ (0 < a ∧ a ≤ n ∧ b ≤ a * (n-a))

private theorem valid_mono {n a b : ℕ} (h : valid n a b) : valid (n+1) a b := by
  rcases h with h | ⟨ha,han,hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨ha, by omega, hb.trans (Nat.mul_le_mul_left a (by omega))⟩

private theorem valid_add {n a b : ℕ} (h : valid n a b) : valid (n+1) (a+1) b := by
  rcases h with ⟨rfl,rfl⟩ | ⟨ha,han,hb⟩
  · exact Or.inr ⟨by omega,by omega,by omega⟩
  · apply Or.inr
    refine ⟨by omega,by omega,?_⟩
    have he : n+1-(a+1) = n-a := by exact Nat.add_sub_add_right n 1 a
    rw [he]
    nlinarith

private theorem valid_mul {n a b : ℕ} (h : valid n a b) : valid (n+1) a (b+a) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨ha,han,hb⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · apply Or.inr
    refine ⟨ha,by omega,?_⟩
    have he : n+1-a = n-a+1 := by exact Nat.sub_add_comm han
    rw [he]
    nlinarith

private theorem valid_predecessor {n a b : ℕ} (ha : 0 < a) (han : a ≤ n+1)
    (hb : b ≤ a * (n+1-a)) :
    (∃ c, valid n c b ∧ c+1=a) ∨
    (∃ d, valid n a d ∧ d+a=b) := by
  by_cases hab : a ≤ b
  · right
    have han' : a ≤ n := by
      by_contra h
      have he : n+1-a=0 := by omega
      rw [he, Nat.mul_zero] at hb
      omega
    refine ⟨b-a, Or.inr ⟨ha,han',?_⟩,by omega⟩
    have he : n+1-a=n-a+1 := by exact Nat.sub_add_comm han'
    rw [he] at hb
    have hh : b-a+a=b := by exact Nat.sub_add_cancel hab
    nlinarith
  · left
    refine ⟨a-1,?_,by omega⟩
    by_cases ha1 : a=1
    · subst a
      have hb0 : b=0 := by exact Nat.eq_zero_of_not_pos hab
      simp [valid,hb0]
    · apply Or.inr
      refine ⟨by omega,by omega,?_⟩
      by_cases han' : a ≤ n
      · have ht : 1 ≤ n-(a-1) := by omega
        have hm := Nat.mul_le_mul_left (a-1) ht
        simp only [Nat.mul_one] at hm
        omega
      · have he : n+1-a=0 := by omega
        rw [he, Nat.mul_zero] at hb
        omega

private theorem seen_spec (n : ℕ) (p : Polynomial ℤ) :
    p ∈ seen n ↔ ∃ a b, p = label a b ∧ valid n a b := by
  classical
  induction n generalizing p with
  | zero =>
    simp only [seen, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨0,0,label_zero.symm,Or.inl ⟨rfl,rfl⟩⟩
    · rintro ⟨a,b,rfl,h⟩
      rcases h with ⟨rfl,rfl⟩ | ⟨ha,han,hb⟩
      · exact label_zero
      · omega
  | succ n ih =>
    simp only [seen, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ((hp | ⟨r,hr,rfl⟩) | ⟨r,hr,rfl⟩)
      · obtain ⟨a,b,rfl,hv⟩ := (ih p).mp hp
        exact ⟨a,b,rfl,valid_mono hv⟩
      · obtain ⟨a,b,rfl,hv⟩ := (ih r).mp hr
        exact ⟨a+1,b,addChild_label a b,valid_add hv⟩
      · obtain ⟨a,b,rfl,hv⟩ := (ih r).mp hr
        exact ⟨a,b+a,mulChild_label a b,valid_mul hv⟩
    · rintro ⟨a,b,rfl,hv⟩
      rcases hv with ⟨rfl,rfl⟩ | ⟨ha,han,hb⟩
      · exact Or.inl (Or.inl ((ih _).mpr ⟨0,0,rfl,Or.inl ⟨rfl,rfl⟩⟩))
      · rcases valid_predecessor ha han hb with ⟨c,hc,hca⟩ | ⟨d,hd,hdb⟩
        · left; right
          exact ⟨label c b,(ih _).mpr ⟨c,b,rfl,hc⟩,by rw [addChild_label,hca]⟩
        · right
          exact ⟨label a d,(ih _).mpr ⟨a,d,rfl,hd⟩,by rw [mulChild_label,hdb]⟩

private theorem label_mem_seen (n a b : ℕ) : label a b ∈ seen n ↔ valid n a b := by
  rw [seen_spec]
  constructor
  · rintro ⟨c,d,h,hv⟩
    have hh := label_injective (show label (a,b).1 (a,b).2 = label (c,d).1 (c,d).2 from h)
    cases hh
    exact hv
  · intro h
    exact ⟨a,b,rfl,h⟩


private theorem generation_succ_spec (n : ℕ) (p : Polynomial ℤ) :
    p ∈ generation (n+1) ↔ p = label (n+1) 0 ∨
      ∃ a b, a ≤ n ∧ a*(n-a) < b ∧ b ≤ a*(n+1-a) ∧ p = label a b := by
  classical
  simp only [generation, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp,hn⟩
    obtain ⟨a,b,rfl,hv⟩ := (seen_spec (n+1) p).mp hp
    rw [label_mem_seen] at hn
    rcases hv with ⟨rfl,rfl⟩ | ⟨ha,han,hb⟩
    · exact False.elim (hn (Or.inl ⟨rfl,rfl⟩))
    · by_cases htop : a=n+1
      · subst a
        have hb0 : b=0 := by simpa using hb
        subst b
        exact Or.inl rfl
      · right
        have han' : a ≤ n := by omega
        refine ⟨a,b,han',?_,hb,rfl⟩
        by_contra hh
        exact hn (Or.inr ⟨ha,han',by omega⟩)
  · rintro (rfl | ⟨a,b,han,hlo,hhi,rfl⟩)
    · rw [label_mem_seen,label_mem_seen]
      constructor
      · exact Or.inr ⟨by omega,by omega,by simp⟩
      · intro h
        rcases h with ⟨ha,hb⟩ | ⟨ha,han,hb⟩ <;> omega
    · rw [label_mem_seen,label_mem_seen]
      have ha : 0<a := by
        by_contra h
        have he : a=0 := by exact Nat.eq_zero_of_not_pos h
        simp [he] at hhi
        omega
      constructor
      · exact Or.inr ⟨ha,by omega,hhi⟩
      · intro h
        rcases h with ⟨he,hb⟩ | ⟨ha,han,hb⟩
        · omega
        · omega

private def shellRows (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (n+1)).sigma (fun a => Finset.Ioc (a*(n-a)) (a*(n+1-a)))


private theorem rowLabel_injective : Function.Injective (fun t : Σ _ : ℕ, ℕ => label t.1 t.2) := by
  intro ⟨a,b⟩ ⟨c,d⟩ h
  have hh := label_injective (show label (a,b).1 (a,b).2 = label (c,d).1 (c,d).2 from h)
  cases hh
  rfl

private theorem generation_succ_eq (n : ℕ) : generation (n+1) =
    insert (label (n+1) 0) ((shellRows n).image (fun t : Σ _ : ℕ, ℕ => label t.1 t.2)) := by
  classical
  ext p
  rw [generation_succ_spec]
  simp only [Finset.mem_insert, Finset.mem_image, shellRows, Finset.mem_sigma,
    Finset.mem_range, Finset.mem_Ioc, Sigma.exists]
  constructor
  · rintro (h | ⟨a,b,ha,hlo,hhi,hp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,b,⟨by omega,hlo,hhi⟩,hp.symm⟩
  · rintro (h | ⟨a,b,⟨ha,hlo,hhi⟩,hp⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,b,by omega,hlo,hhi,hp.symm⟩

private theorem top_not_in_rows (n : ℕ) : label (n+1) 0 ∉ (shellRows n).image (fun t : Σ _ : ℕ, ℕ => label t.1 t.2) := by
  classical
  rintro h
  obtain ⟨⟨a,b⟩,hm,he⟩ := Finset.mem_image.mp h
  have hh := label_injective (show label (a,b).1 (a,b).2 = label (n+1,0).1 (n+1,0).2 from he)
  have ha : a=n+1 := congrArg Prod.fst hh
  have hr : a<n+1 := Finset.mem_range.mp (Finset.mem_sigma.mp hm).1
  omega

private theorem G_succ (n : ℕ) : G (n+1) = 1 + ∑ a ∈ Finset.range (n+1), a := by
  classical
  unfold G
  rw [generation_succ_eq, Finset.card_insert_of_notMem (top_not_in_rows n),
    Finset.card_image_of_injective _ rowLabel_injective]
  unfold shellRows
  rw [Finset.card_sigma]
  have he : ∀ a ∈ Finset.range (n+1),
      (Finset.Ioc (a*(n-a)) (a*(n+1-a))).card = a := by
    intro a ha
    have han : a≤n := by exact Finset.mem_range_succ_iff.mp ha
    have hs : n+1-a=n-a+1 := by exact Nat.sub_add_comm han
    rw [Nat.card_Ioc,hs,Nat.mul_add,Nat.mul_one,Nat.add_sub_cancel_left]
  rw [Finset.sum_congr rfl he]
  omega

private theorem G_zero : G 0 = 1 := by
  exact Finset.card_singleton (0 : Polynomial ℤ)

private theorem G_sum (n : ℕ) : G n = 1 + ∑ a ∈ Finset.range n, a := by
  cases n with
  | zero => simp [G_zero]
  | succ n => exact G_succ n

private theorem G_difference (n : ℕ) : G (n+1) = G n + n := by
  rw [G_sum,G_sum,Finset.sum_range_succ]
  omega

theorem result : claim := by
  refine ⟨3,by omega,?_⟩
  intro n hn
  have h1 := G_difference (n-1)
  have h2 := G_difference (n-2)
  have h3 := G_difference (n-3)
  have e1 : n-1+1=n := by omega
  have e2 : n-2+1=n-1 := by omega
  have e3 : n-3+1=n-2 := by omega
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h1z : (G n : ℤ) = (G (n-1) : ℤ) + (n-1 : ℕ) := by exact congrArg Nat.cast h1
  have h2z : (G (n-1) : ℤ) = (G (n-2) : ℤ) + (n-2 : ℕ) := by exact congrArg Nat.cast h2
  have h3z : (G (n-2) : ℤ) = (G (n-3) : ℤ) + (n-3 : ℕ) := by exact congrArg Nat.cast h3
  have hh : ((n-1 : ℕ) : ℤ) - 2*((n-2 : ℕ) : ℤ) + ((n-3 : ℕ) : ℤ) = 0 := by omega
  omega


end
end D5.S3.Combinatorics.PolynomialTrees.BallotKimberlingMosesDoubleRootGeneration
