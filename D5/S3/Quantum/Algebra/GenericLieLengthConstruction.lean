/- GID: D5/S3/Quantum/Algebra/GenericLieLengthConstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GenericLieLengthConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Algebra/GenericLieLength.result; premises=D5/S3/Quantum/Algebra/GenericLieLengthConstruction.gapSet_card
   digest: Jia-Capel generic Lie length conjecture formalization. -/
/- admission_basis: escape-witness
   Direct frozen dependencies: none; every D5 proof dependency is in this delivery.
   Module witnesses: anchored_units_mem.
   Heap depth uses Nat.size; coordinate and matrix operations use their Mathlib owners.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16180
   heapColor: proof_shape: bind-only; escape_witness: none; consumers: T,T_transpose,T_zero_row,anchored_units_mem,bulk_edge_color_ne,bulk_energy_ne,bulk_gap,child_color_unique,color_child_ne,color_even,color_lt,color_odd,color_one,color_pair_gap_iff,color_siblings_ne,energy,energy_bounds,energy_eq_colorValue,energy_one,energy_zero,neighbor_of_child_color,transfer_column,transfer_row,transfer_selector.
   color_lt: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem,bulk_energy_ne,color_child_ne,color_pair_gap_iff,color_siblings_ne.
   color_one: proof_shape: bind-only; escape_witness: none; consumers: energy_one.
   color_even: proof_shape: bind-only; escape_witness: none; consumers: color_siblings_ne.
   color_odd: proof_shape: bind-only; escape_witness: none; consumers: color_siblings_ne.
   color_child_ne: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem,bulk_edge_color_ne,bulk_energy_ne.
   color_siblings_ne: proof_shape: bind-only; escape_witness: none; consumers: child_color_unique.
   energy: proof_shape: bind-only; escape_witness: none; consumers: A_hermitian,A_trace,anchor_forward_selector,anchor_reverse_selector,anchor_unique,bulk_energy_ne,bulk_gap,centeredEnergy,centered_gap,color_pair_gap_iff,complex_edge_gap,edge_gap,energy_bounds,energy_eq_colorValue,energy_one,energy_zero,meanEnergy,selector_entry,transfer_selector.
   energy_zero: proof_shape: bind-only; escape_witness: none; consumers: anchor_unique,color_pair_gap_iff,edge_gap.
   energy_one: proof_shape: bind-only; escape_witness: none; consumers: anchor_unique,color_pair_gap_iff,edge_gap.
   energy_bounds: proof_shape: bind-only; escape_witness: none; consumers: anchor_unique.
   heapEdge: proof_shape: bind-only; escape_witness: none; consumers: B,B_apply,B_hermitian,B_trace,T,T_transpose,T_zero_row,anchor_forward_selector,anchor_reverse_selector,anchor_unique,bulk_edge_color_ne,color_pair_gap_iff,complex_edge_gap,edge_gap,edge_ne,edge_symm,heapEdgeDecidable,neighbor_of_child_color,selector_entry,transfer_column,transfer_selector.
   heapEdgeDecidable: proof_shape: bind-only; escape_witness: none; consumers: B,B_apply,B_hermitian,B_trace,T,T_transpose,T_zero_row,anchor_forward_selector,anchor_reverse_selector,selector_entry,transfer_column,transfer_selector.
   edge_symm: proof_shape: bind-only; escape_witness: none; consumers: B_apply,B_hermitian,T_transpose.
   edge_ne: proof_shape: bind-only; escape_witness: none; consumers: B_apply.
   bulk_energy_ne: proof_shape: bind-only; escape_witness: none; consumers: bulk_gap.
   gapSet: proof_shape: bind-only; escape_witness: none; consumers: anchor_forward_selector,anchor_reverse_selector,anchor_units_mem,bulk_gap,color_gap_mem,complex_edge_gap,edge_gap,gapSet_card,selector_entry,selector_mem_eight,transferGap_mem,transfer_mem_eight,transfer_selector.
   bulk_gap: proof_shape: bind-only; escape_witness: none; consumers: edge_gap.
   edge_gap: proof_shape: bind-only; escape_witness: none; consumers: complex_edge_gap.
   anchor_unique: proof_shape: bind-only; escape_witness: none; consumers: anchor_forward_selector,anchor_reverse_selector.
   child_color_unique: proof_shape: bind-only; escape_witness: none; consumers: neighbor_of_child_color.
   neighbor_of_child_color: proof_shape: bind-only; escape_witness: none; consumers: transfer_column.
   colorValue: proof_shape: bind-only; escape_witness: none; consumers: colorValue_bounds,color_difference_injective,color_gap_mem,color_pair_gap_iff,transferGap,transferGap_mem,transfer_selector.
   colorValue_bounds: proof_shape: bind-only; escape_witness: none; consumers: color_pair_gap_iff.
   energy_eq_colorValue: proof_shape: bind-only; escape_witness: none; consumers: color_pair_gap_iff.
   color_difference_injective: proof_shape: bind-only; escape_witness: none; consumers: color_pair_gap_iff.
   color_gap_mem: proof_shape: bind-only; escape_witness: none; consumers: transferGap_mem.
   bulk_edge_color_ne: proof_shape: bind-only; escape_witness: none; consumers: color_pair_gap_iff.
   color_pair_gap_iff: proof_shape: bind-only; escape_witness: none; consumers: transfer_selector.
   size_eq_log: proof_shape: bind-only; escape_witness: none; consumers: depth_bound,depth_parent.
   depth_parent: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem.
   depth_bound: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_uniform.
   adDiagonal_entry: proof_shape: bind-only; escape_witness: none; consumers: adDiagonal_single.
   adDiagonal_single: proof_shape: bind-only; escape_witness: none; consumers: polynomial_adDiagonal_single.
   polynomial_adDiagonal_single: proof_shape: bind-only; escape_witness: none; consumers: polynomial_adDiagonal_entry.
   polynomial_adDiagonal_entry: proof_shape: bind-only; escape_witness: none; consumers: selector_apply.
   selector_eval: proof_shape: bind-only; escape_witness: none; consumers: selector_apply.
   selector_natDegree: proof_shape: bind-only; escape_witness: none; consumers: selector_mem_eight.
   selector_apply: proof_shape: bind-only; escape_witness: none; consumers: selector_entry.
   meanEnergy: proof_shape: bind-only; escape_witness: none; consumers: centeredEnergy,centered_gap.
   centeredEnergy: proof_shape: bind-only; escape_witness: none; consumers: A,A_hermitian,A_trace,anchor_forward_selector,anchor_reverse_selector,anchor_units_mem,centered_gap,complex_edge_gap,selector_entry,selector_mem_eight,transfer_mem_eight,transfer_selector.
   A: proof_shape: bind-only; escape_witness: none; consumers: A_trace,gen.
   B: proof_shape: bind-only; escape_witness: none; consumers: B_apply,B_hermitian,B_trace,anchor_forward_selector,anchor_reverse_selector,anchor_units_mem,gen,selector_entry,selector_mem_eight,transfer_mem_eight,transfer_selector.
   B_apply: proof_shape: bind-only; escape_witness: none; consumers: B_hermitian,anchor_forward_selector,anchor_reverse_selector,selector_entry,transfer_selector.
   gen: proof_shape: bind-only; escape_witness: none; consumers: B_mem,adjusted_units_mem,anchor_units_mem,anchored_units_mem,anchored_units_uniform,iGen,iGen_su,real_full_span,selector_mem_eight,traceless_full_span,transfer_mem_eight.
   centered_gap: proof_shape: bind-only; escape_witness: none; consumers: complex_edge_gap,selector_entry.
   complex_edge_gap: proof_shape: bind-only; escape_witness: none; consumers: selector_entry.
   gapSet_card: proof_shape: bind-only; escape_witness: none; consumers: selector_mem_eight.
   B_mem: proof_shape: bind-only; escape_witness: none; consumers: selector_mem_eight.
   selector_mem_eight: proof_shape: bind-only; escape_witness: none; consumers: anchor_units_mem,transfer_mem_eight.
   selector_entry: proof_shape: bind-only; escape_witness: none; consumers: anchor_forward_selector,anchor_reverse_selector,transfer_selector.
   anchor_forward_selector: proof_shape: bind-only; escape_witness: none; consumers: anchor_units_mem.
   anchor_reverse_selector: proof_shape: bind-only; escape_witness: none; consumers: anchor_units_mem.
   anchor_units_mem: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem.
   T: proof_shape: bind-only; escape_witness: none; consumers: T_transpose,T_zero_row,anchored_units_mem,transfer_column,transfer_mem_eight,transfer_row,transfer_selector.
   transferGap: proof_shape: bind-only; escape_witness: none; consumers: transferGap_mem,transfer_mem_eight,transfer_selector.
   transferGap_mem: proof_shape: bind-only; escape_witness: none; consumers: transfer_mem_eight,transfer_selector.
   transfer_selector: proof_shape: bind-only; escape_witness: none; consumers: transfer_mem_eight.
   transfer_mem_eight: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem.
   T_zero_row: proof_shape: bind-only; escape_witness: none; consumers: transfer_column.
   T_transpose: proof_shape: bind-only; escape_witness: none; consumers: transfer_row.
   parent: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem,transfer_column,transfer_row.
   bracket_column_entry: proof_shape: bind-only; escape_witness: none; consumers: transfer_column.
   transfer_column: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem,transfer_row.
   transfer_row: proof_shape: bind-only; escape_witness: none; consumers: anchored_units_mem.
   anchored_units_mem: proof_shape: content; escape_witness: anchored_units_mem; consumers: anchored_units_uniform.
   anchored_bracket: proof_shape: bind-only; escape_witness: none; consumers: adjusted_units_mem.
   trace_zero_mem_of_adjusted_units: proof_shape: bind-only; escape_witness: none; consumers: traceless_full_span.
   anchored_units_uniform: proof_shape: content; escape_witness: anchored_units_mem; consumers: adjusted_units_mem.
   adjusted_units_mem: proof_shape: content; escape_witness: anchored_units_mem; consumers: traceless_full_span.
   traceless_full_span: proof_shape: content; escape_witness: anchored_units_mem; consumers: real_full_span.
   word_scaled: proof_shape: bind-only; escape_witness: none; consumers: rightSpan_le_scaled.
   rightSpan_le_scaled: proof_shape: bind-only; escape_witness: none; consumers: real_full_span.
   A_hermitian: proof_shape: bind-only; escape_witness: none; consumers: iGen_su.
   A_trace: proof_shape: bind-only; escape_witness: none; consumers: iGen_su.
   B_hermitian: proof_shape: bind-only; escape_witness: none; consumers: iGen_su.
   B_trace: proof_shape: bind-only; escape_witness: none; consumers: iGen_su.
   iGen: proof_shape: bind-only; escape_witness: none; consumers: compactPair,iGen_su,real_full_span.
   imaginary_hermitian_mem: proof_shape: bind-only; escape_witness: none; consumers: iGen_su.
   iGen_su: proof_shape: bind-only; escape_witness: none; consumers: compactPair,real_full_span.
   real_full_span: proof_shape: content; escape_witness: anchored_units_mem; consumers: compactPair_span_top.
   suLieRing: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,compactPair_span_top,extendedPair_span_top,suLieAlgebra.
   suLieAlgebra: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,compactPair_span_top,extendedPair_span_top.
   word_map: proof_shape: bind-only; escape_witness: none; consumers: rightSpan_map.
   rightSpan_map: proof_shape: bind-only; escape_witness: none; consumers: ae_rightSpan_eq,compactPair_span_top.
   compactPair: proof_shape: bind-only; escape_witness: none; consumers: compactPair_span_top,extendedPair,extendedPair_span_top.
   compactPair_span_top: proof_shape: content; escape_witness: anchored_units_mem; consumers: extendedPair_span_top.
-/


import D5.S3.Quantum.Algebra.GenericLieLengthFiltration
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Nat.Size
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Hermitian



namespace D5.S3.Quantum.Algebra.GenericLieLengthConstruction

noncomputable section



def heapColor (v : ℕ) : ℕ :=
  if v ≤ 1 then 0 else (heapColor (v / 2) + if v % 2 = 0 then 1 else 2) % 3
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

private theorem color_lt (v : ℕ) : heapColor v < 3 := by
  rw [heapColor]
  split_ifs <;> omega

@[simp] private theorem color_one : heapColor 1 = 0 := by rw [heapColor]; simp

private theorem color_even (v : ℕ) (hv : 1 ≤ v) :
    heapColor (2 * v) = (heapColor v + 1) % 3 := by
  rw [heapColor]
  have h : ¬2 * v ≤ 1 := by omega
  simp [h, Nat.mul_div_right, Nat.mul_mod]

private theorem color_odd (v : ℕ) (hv : 1 ≤ v) :
    heapColor (2 * v + 1) = (heapColor v + 2) % 3 := by
  rw [heapColor]
  have h : ¬2 * v + 1 ≤ 1 := by omega
  have hd : (2 * v + 1) / 2 = v := by omega
  have hm : (2 * v + 1) % 2 = 1 := by omega
  simp [h, hd, hm]

private theorem color_child_ne (v : ℕ) (hv : 2 ≤ v) : heapColor v ≠ heapColor (v / 2) := by
  rw [heapColor]
  have h : ¬v ≤ 1 := by omega
  rw [if_neg h]
  have hc := color_lt (v / 2)
  split_ifs <;> omega

private theorem color_siblings_ne (v : ℕ) (hv : 1 ≤ v) :
    heapColor (2 * v) ≠ heapColor (2 * v + 1) := by
  rw [color_even v hv, color_odd v hv]
  have hc := color_lt v
  omega

def energy (v : ℕ) : ℤ :=
  if v = 0 then 7 else if heapColor v = 0 then 0 else if heapColor v = 1 then 1 else 3

@[simp] private theorem energy_zero : energy 0 = 7 := by simp [energy]
@[simp] private theorem energy_one : energy 1 = 0 := by simp [energy]

private theorem energy_bounds (v : ℕ) (hv : 1 ≤ v) : 0 ≤ energy v ∧ energy v ≤ 3 := by
  have h : v ≠ 0 := by omega
  simp only [energy, if_neg h]
  split_ifs <;> omega

def heapEdge (u v : ℕ) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (2 ≤ u ∧ u / 2 = v) ∨ (2 ≤ v ∧ v / 2 = u)

private instance heapEdgeDecidable (u v : ℕ) : Decidable (heapEdge u v) := by unfold heapEdge; infer_instance

private theorem edge_symm (u v : ℕ) : heapEdge u v ↔ heapEdge v u := by
  unfold heapEdge
  tauto

private theorem edge_ne (u v : ℕ) (h : heapEdge u v) : u ≠ v := by
  rcases h with h | h | h | h <;> omega

private theorem bulk_energy_ne (u : ℕ) (hu : 2 ≤ u) : energy u ≠ energy (u / 2) := by
  have hc := color_child_ne u hu
  have hcu := color_lt u
  have hcp := color_lt (u / 2)
  have h0 : u ≠ 0 := by omega
  have hp0 : u / 2 ≠ 0 := by omega
  simp only [energy, if_neg h0, if_neg hp0]
  split_ifs <;> omega

private def gapSet : Finset ℤ := {-7, -3, -2, -1, 1, 2, 3, 7}

private theorem bulk_gap (u : ℕ) (hu : 2 ≤ u) : energy u - energy (u / 2) ∈ gapSet := by
  have hc := bulk_energy_ne u hu
  have h0 : u ≠ 0 := by omega
  have hp0 : u / 2 ≠ 0 := by omega
  simp only [energy, if_neg h0, if_neg hp0] at hc ⊢
  simp only [gapSet, Finset.mem_insert, Finset.mem_singleton]
  split_ifs at hc ⊢ <;> omega

private theorem edge_gap (u v : ℕ) (h : heapEdge u v) : energy u - energy v ∈ gapSet := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hu, rfl⟩ | ⟨hv, rfl⟩
  · norm_num [gapSet]
  · norm_num [gapSet]
  · exact bulk_gap u hu
  · have h := bulk_gap v hv
    simp only [gapSet, Finset.mem_insert, Finset.mem_singleton] at h ⊢
    omega

private theorem anchor_unique (u v : ℕ) (h : heapEdge u v) :
    (energy u - energy v = 7 ↔ u = 0 ∧ v = 1) ∧
    (energy u - energy v = -7 ↔ u = 1 ∧ v = 0) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hu, rfl⟩ | ⟨hv, rfl⟩
  · norm_num
  · norm_num
  · have h1 := energy_bounds u (by omega)
    have h2 := energy_bounds (u / 2) (by omega)
    omega
  · have h1 := energy_bounds v (by omega)
    have h2 := energy_bounds (v / 2) (by omega)
    omega

private theorem child_color_unique (v i w : ℕ) (hv : 1 ≤ v)
    (hi : i / 2 = v) (hw : w / 2 = v) (hc : heapColor i = heapColor w) : i = w := by
  have hi' : i = 2 * v ∨ i = 2 * v + 1 := by omega
  have hw' : w = 2 * v ∨ w = 2 * v + 1 := by omega
  have hs := color_siblings_ne v hv
  rcases hi' with rfl | rfl <;> rcases hw' with rfl | rfl <;> simp_all

private theorem neighbor_of_child_color (v i w : ℕ) (hv : 1 ≤ v) (hw : 2 ≤ w)
    (hwp : w / 2 = v) (hi : 1 ≤ i) :
    (heapEdge i v ∧ heapColor i = heapColor w) ↔
      i = w ∨ (2 ≤ v ∧ i = v / 2 ∧ heapColor (v / 2) = heapColor w) := by
  constructor
  · rintro ⟨he, hc⟩
    rcases he with ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨hi2, hip⟩ | ⟨hv2, hvp⟩
    · omega
    · omega
    · exact Or.inl (child_color_unique v i w hv hip hwp hc)
    · exact Or.inr ⟨hv2, hvp.symm, by simpa [hvp] using hc⟩
  · rintro (rfl | ⟨hv2, rfl, hc⟩)
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨hw, hwp⟩)), rfl⟩
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨hv2, rfl⟩)), hc⟩

private def colorValue (a : ℕ) : ℤ := if a = 0 then 0 else if a = 1 then 1 else 3

private theorem colorValue_bounds (a : ℕ) : 0 ≤ colorValue a ∧ colorValue a ≤ 3 := by
  unfold colorValue
  split_ifs <;> omega

private theorem energy_eq_colorValue (v : ℕ) (hv : 1 ≤ v) : energy v = colorValue (heapColor v) := by
  simp [energy, colorValue, show v ≠ 0 by omega]

private theorem color_difference_injective (a b c d : ℕ) (ha : a < 3) (hb : b < 3)
    (hc : c < 3) (hd : d < 3) (hab : a ≠ b) (hcd : c ≠ d)
    (h : colorValue b - colorValue a = colorValue d - colorValue c) : a = c ∧ b = d := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    norm_num [colorValue] at *

private theorem color_gap_mem (a b : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    colorValue b - colorValue a ∈ gapSet := by
  interval_cases a <;> interval_cases b <;> norm_num [colorValue, gapSet] at *

private theorem bulk_edge_color_ne (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (he : heapEdge u v) :
    heapColor u ≠ heapColor v := by
  rcases he with ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨hu2, rfl⟩ | ⟨hv2, rfl⟩
  · omega
  · omega
  · exact color_child_ne u hu2
  · exact Ne.symm (color_child_ne v hv2)

private theorem color_pair_gap_iff (u v a b : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b)
    (he : heapEdge u v) :
    (energy u - energy v = colorValue b - colorValue a) ↔
      (1 ≤ u ∧ 1 ≤ v ∧ heapColor u = b ∧ heapColor v = a) := by
  by_cases hu : u = 0
  · subst u
    have hv : v = 1 := by rcases he with he | he | he | he <;> omega
    subst v
    have ha' := colorValue_bounds a
    have hb' := colorValue_bounds b
    simp only [energy_zero, energy_one]
    omega
  by_cases hv : v = 0
  · subst v
    have hu' : u = 1 := by rcases he with he | he | he | he <;> omega
    subst u
    have ha' := colorValue_bounds a
    have hb' := colorValue_bounds b
    simp only [energy_zero, energy_one]
    omega
  have hup : 1 ≤ u := by omega
  have hvp : 1 ≤ v := by omega
  rw [energy_eq_colorValue u hup, energy_eq_colorValue v hvp]
  have hne := bulk_edge_color_ne u v hup hvp he
  constructor
  · intro h
    have hh := color_difference_injective (heapColor v) (heapColor u) a b
      (color_lt v) (color_lt u) ha hb (Ne.symm hne) hab h
    exact ⟨hup, hvp, hh.2, hh.1⟩
  · rintro ⟨_, _, hcu, hcv⟩
    simp [hcu, hcv]

private theorem size_eq_log (v : ℕ) : Nat.size v = if v = 0 then 0 else 1 + Nat.log 2 v := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv]
    have hup : v < 2 ^ (Nat.log 2 v + 1) := Nat.lt_pow_succ_log_self (by decide) v
    have hlo : 2 ^ Nat.log 2 v ≤ v := Nat.pow_log_le_self 2 hv
    have h1 := Nat.size_le.mpr hup
    have h2 := Nat.lt_size.mpr hlo
    omega


private theorem depth_parent (v : ℕ) (hv : 2 ≤ v) : Nat.size (v / 2) + 1 = Nat.size v := by
  have h0 : v ≠ 0 := by omega
  have hp0 : v / 2 ≠ 0 := by omega
  have hlog : 1 ≤ Nat.log 2 v := Nat.log_pos (by omega) hv
  simp only [size_eq_log, if_neg h0, if_neg hp0, Nat.log_div_base]
  omega

private theorem depth_bound (n v : ℕ) (hv : v < n) : Nat.size v ≤ 1 + Nat.log 2 (n - 1) := by
  by_cases h0 : v = 0
  · simp [h0]
  · have hle : v ≤ n - 1 := by omega
    simpa only [size_eq_log, if_neg h0] using Nat.add_le_add_left (Nat.log_mono_right (b := 2) hle) 1


attribute [local instance] LieRing.ofAssociativeRing

open Matrix Polynomial

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] [DecidableEq K]


private theorem adDiagonal_entry (h : I → K) (X : Matrix I I K) (i j : I) :
    (LieAlgebra.ad K (Matrix I I K) (Matrix.diagonal h)) X i j = (h i - h j) * X i j := by
  simp [LieAlgebra.ad_apply, Ring.lie_def, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private theorem adDiagonal_single (h : I → K) (i j : I) (a : K) :
    (LieAlgebra.ad K (Matrix I I K) (Matrix.diagonal h)) (Matrix.single i j a) = (h i - h j) • Matrix.single i j a := by
  ext u v
  rw [adDiagonal_entry]
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [Matrix.single, hi, hj, Matrix.smul_apply, smul_eq_mul]

private theorem polynomial_adDiagonal_single (h : I → K) (p : K[X]) (i j : I) (a : K) :
    Polynomial.aeval ((LieAlgebra.ad K (Matrix I I K) (Matrix.diagonal h))) p (Matrix.single i j a) =
      p.eval (h i - h j) • Matrix.single i j a :=
  Module.End.aeval_apply_of_mem_apply_eq_smul (adDiagonal_single h i j a)

private theorem polynomial_adDiagonal_entry (h : I → K) (p : K[X]) (X : Matrix I I K)
    (i j : I) :
    Polynomial.aeval ((LieAlgebra.ad K (Matrix I I K) (Matrix.diagonal h))) p X i j = p.eval (h i - h j) * X i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply, polynomial_adDiagonal_single,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.single, ite_and, eq_comm]


private theorem selector_eval (delta : Finset K) (d e : K) (hd : d ∈ delta) (he : e ∈ delta) :
    (Lagrange.basis delta id d).eval e = if d = e then 1 else 0 := by
  by_cases hde : d = e
  · subst e
    simpa [Lagrange.basis] using (Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hd)
  · simpa [ hde] using Lagrange.eval_basis_of_ne (v := id) hde he

private theorem selector_natDegree (delta : Finset K) (d : K) (hd : d ∈ delta) :
    (Lagrange.basis delta id d).natDegree = delta.card - 1 :=
  Lagrange.natDegree_basis (Set.injOn_id _) hd

private theorem selector_apply (h : I → K) (B : Matrix I I K) (delta : Finset K) (d : K)
    (hd : d ∈ delta) (hgap : ∀ i j, B i j ≠ 0 → h i - h j ∈ delta) :
    Polynomial.aeval ((LieAlgebra.ad K (Matrix I I K) (Matrix.diagonal h))) (Lagrange.basis delta id d) B =
      fun i j => if h i - h j = d then B i j else 0 := by
  ext i j
  rw [polynomial_adDiagonal_entry]
  by_cases hb : B i j = 0
  · simp [hb]
  · rw [selector_eval delta d (h i - h j) hd (hgap i j hb)]
    by_cases he : h i - h j = d
    · simp [he]
    · simp [he, Ne.symm he]


open Matrix Polynomial D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthConstruction

attribute [local instance] LieRing.ofAssociativeRing


def meanEnergy (n : ℕ) : ℂ := (∑ v : Fin (n + 2), (energy v.val : ℂ)) / (n + 2)

def centeredEnergy (n : ℕ) (v : Fin (n + 2)) : ℂ := (energy v.val : ℂ) - meanEnergy n

def A (n : ℕ) : (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) := Matrix.diagonal (centeredEnergy n)

def B (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := by
  classical
  exact (SimpleGraph.fromRel (fun i j : Fin (n + 2) => heapEdge i.val j.val)).adjMatrix ℂ

private theorem B_apply (n : ℕ) (i j : Fin (n + 2)) :
    B n i j = if heapEdge i.val j.val then 1 else 0 := by
  classical
  simp only [B, SimpleGraph.adjMatrix_apply, SimpleGraph.fromRel_adj,
    edge_symm j.val i.val, or_self]
  by_cases h : heapEdge i.val j.val
  · have hn : i ≠ j := fun he => edge_ne _ _ h (congrArg Fin.val he)
    simp [h, hn]
  · simp [h]

def gen (n : ℕ) : Fin 2 → (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) := ![A n, B n]

private theorem centered_gap (n : ℕ) (i j : Fin (n + 2)) :
    centeredEnergy n i - centeredEnergy n j = (energy i.val : ℂ) - (energy j.val : ℂ) := by
  unfold centeredEnergy
  ring

private theorem complex_edge_gap (n : ℕ) (i j : Fin (n + 2)) (he : heapEdge i.val j.val) :
    centeredEnergy n i - centeredEnergy n j ∈ (gapSet.image (Int.cast : ℤ → ℂ)) := by
  rw [centered_gap]
  have h := edge_gap i.val j.val he
  refine Finset.mem_image.mpr ⟨energy i.val - energy j.val, h, ?_⟩
  push_cast
  rfl

private theorem gapSet_card : (gapSet.image (Int.cast : ℤ → ℂ)).card = 8 := by norm_num [gapSet]

private theorem B_mem (n : ℕ) : B n ∈ rightSpan (K := ℂ) (gen n) 1 := by
  exact word_mem (gen n) (.single 1) 1 (by simp [rightWordLength])

private theorem selector_mem_eight (n : ℕ) (d : ℂ) (hd : d ∈ (gapSet.image (Int.cast : ℤ → ℂ))) :
    Polynomial.aeval ((LieAlgebra.ad ℂ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (Matrix.diagonal (centeredEnergy n)))) (Lagrange.basis (gapSet.image (Int.cast : ℤ → ℂ)) id d) (B n) ∈
      rightSpan (K := ℂ) (gen n) 8 := by
  have h := polynomial_ad_mem (gen n) (0 : Fin 2) (B_mem n) (Lagrange.basis (gapSet.image (Int.cast : ℤ → ℂ)) id d)
  simpa [gen, A, selector_natDegree (gapSet.image (Int.cast : ℤ → ℂ)) d hd, gapSet_card] using h

private theorem selector_entry (n : ℕ) (d : ℂ) (hd : d ∈ (gapSet.image (Int.cast : ℤ → ℂ))) :
    Polynomial.aeval ((LieAlgebra.ad ℂ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (Matrix.diagonal (centeredEnergy n)))) (Lagrange.basis (gapSet.image (Int.cast : ℤ → ℂ)) id d) (B n) =
      fun i j => if (energy i.val : ℂ) - (energy j.val : ℂ) = d then B n i j else 0 := by
  rw [selector_apply (centeredEnergy n) (B n) (gapSet.image (Int.cast : ℤ → ℂ)) d hd]
  · ext i j
    simp only [centered_gap]
  · intro i j hb
    apply complex_edge_gap n i j
    by_contra he
    exact hb (by simp [B_apply, he])

private theorem anchor_forward_selector (n : ℕ) :
    Polynomial.aeval ((LieAlgebra.ad ℂ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (Matrix.diagonal (centeredEnergy n)))) (Lagrange.basis (gapSet.image (Int.cast : ℤ → ℂ)) id 7) (B n) =
      Matrix.single (0 : Fin (n + 2)) 1 (1 : ℂ) := by
  rw [selector_entry n 7 (by norm_num [gapSet])]
  ext i j
  by_cases he : heapEdge i.val j.val
  · have h := (anchor_unique i.val j.val he).1
    have hc : (energy i.val : ℂ) - (energy j.val : ℂ) = 7 ↔ i.val = 0 ∧ j.val = 1 := by
      exact_mod_cast h
    have hz : i.val = 0 ↔ i = 0 := by simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one]
    have ho : j.val = 1 ↔ j = 1 := by simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one]
    simp [B_apply, he, hc, hz, ho, Matrix.single, eq_comm]
  · have h0 : ¬ (i = 0 ∧ j = 1) := by
      rintro ⟨rfl, rfl⟩
      exact he (by simp [heapEdge])
    simp [B_apply, he, Matrix.single, h0, eq_comm]

private theorem anchor_reverse_selector (n : ℕ) :
    Polynomial.aeval ((LieAlgebra.ad ℂ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (Matrix.diagonal (centeredEnergy n)))) (Lagrange.basis (gapSet.image (Int.cast : ℤ → ℂ)) id (-7)) (B n) =
      Matrix.single (1 : Fin (n + 2)) 0 (1 : ℂ) := by
  rw [selector_entry n (-7) (by norm_num [gapSet])]
  ext i j
  by_cases he : heapEdge i.val j.val
  · have h := (anchor_unique i.val j.val he).2
    have hc : (energy i.val : ℂ) - (energy j.val : ℂ) = -7 ↔ i.val = 1 ∧ j.val = 0 := by
      exact_mod_cast h
    have ho : i.val = 1 ↔ i = 1 := by simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one]
    have hz : j.val = 0 ↔ j = 0 := by simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one]
    simp [B_apply, he, hc, hz, ho, Matrix.single, eq_comm]
  · have h0 : ¬ (i = 1 ∧ j = 0) := by
      rintro ⟨rfl, rfl⟩
      exact he (by simp [heapEdge])
    simp [B_apply, he, Matrix.single, h0, eq_comm]

private theorem anchor_units_mem (n : ℕ) :
    Matrix.single (0 : Fin (n + 2)) 1 (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) 8 ∧
    Matrix.single (1 : Fin (n + 2)) 0 (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) 8 := by
  constructor
  · rw [← anchor_forward_selector]
    exact selector_mem_eight n 7 (by norm_num [gapSet])
  · rw [← anchor_reverse_selector]
    exact selector_mem_eight n (-7) (by norm_num [gapSet])

private def T (n b a : ℕ) : (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) := fun i j =>
  if 1 ≤ i.val ∧ 1 ≤ j.val ∧ heapEdge i.val j.val ∧ heapColor i.val = b ∧ heapColor j.val = a
  then 1 else 0

private def transferGap (b a : ℕ) : ℂ := ((colorValue b - colorValue a : ℤ) : ℂ)

private theorem transferGap_mem (b a : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    transferGap b a ∈ (gapSet.image (Int.cast : ℤ → ℂ)) := by
  exact Finset.mem_image.mpr ⟨colorValue b - colorValue a,
    color_gap_mem a b ha hb hab, rfl⟩

private theorem transfer_selector (n b a : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    Polynomial.aeval ((LieAlgebra.ad ℂ (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (Matrix.diagonal (centeredEnergy n))))
      (Lagrange.basis (gapSet.image (Int.cast : ℤ → ℂ)) id (transferGap b a)) (B n) = T n b a := by
  rw [selector_entry n (transferGap b a) (transferGap_mem b a ha hb hab)]
  ext i j
  by_cases he : heapEdge i.val j.val
  · have h := color_pair_gap_iff i.val j.val a b ha hb hab he
    have hc : (energy i.val : ℂ) - (energy j.val : ℂ) = transferGap b a ↔
        1 ≤ i.val ∧ 1 ≤ j.val ∧ heapColor i.val = b ∧ heapColor j.val = a := by
      dsimp [transferGap]
      exact_mod_cast h
    simp [B_apply, T, he, hc, and_assoc]
  · simp [B_apply, T, he]

private theorem transfer_mem_eight (n b a : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    T n b a ∈ rightSpan (K := ℂ) (gen n) 8 := by
  rw [← transfer_selector n b a ha hb hab]
  exact selector_mem_eight n (transferGap b a) (transferGap_mem b a ha hb hab)

private theorem T_zero_row (n b a : ℕ) (j : Fin (n + 2)) : T n b a 0 j = 0 := by simp [T]

private theorem T_transpose (n b a : ℕ) : (T n b a).transpose = T n a b := by
  ext i j
  simp only [Matrix.transpose_apply, T, edge_symm j.val i.val]
  congr 1
  apply propext
  tauto

private def parent (n : ℕ) (v : Fin (n + 2)) : Fin (n + 2) :=
  ⟨v.val / 2, (Nat.div_le_self _ _).trans_lt v.isLt⟩

private theorem bracket_column_entry (n : ℕ) (M : (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)) (hz : ∀ j, M 0 j = 0)
    (v i j : Fin (n + 2)) :
    (⁅M, Matrix.single v (0 : Fin (n + 2)) (1 : ℂ)⁆) i j = if j = 0 then M i v else 0 := by
  by_cases hj : j = 0
  · subst j
    simp [Ring.lie_def, Matrix.mul_apply, Matrix.single, ite_and, hz, eq_comm]
  · simp [Ring.lie_def, Matrix.mul_apply, Matrix.single, ite_and, hz, hj, Ne.symm hj]

private theorem transfer_column (n : ℕ) (v w : Fin (n + 2)) (hv : 1 ≤ v.val)
    (hw : 2 ≤ w.val) (hwp : w.val / 2 = v.val) :
    ⁅T n (heapColor w.val) (heapColor v.val), Matrix.single v (0 : Fin (n + 2)) (1 : ℂ)⁆ =
      Matrix.single w (0 : Fin (n + 2)) (1 : ℂ) +
        if 2 ≤ v.val ∧ heapColor (v.val / 2) = heapColor w.val
        then Matrix.single (parent n v) (0 : Fin (n + 2)) (1 : ℂ) else 0 := by
  ext i j
  rw [bracket_column_entry n _ (T_zero_row n _ _) v i j]
  by_cases hj : j = 0
  · subst j
    have hneigh := neighbor_of_child_color v.val i.val w.val hv hw hwp
    have hwpne : w ≠ parent n v := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [parent] at hh
      omega
    have hval : i.val = w.val ↔ i = w := Fin.ext_iff.symm
    have hpar : i.val = v.val / 2 ↔ i = parent n v := by
      simpa only [parent] using (Fin.ext_iff (a := i) (b := parent n v)).symm
    by_cases hi : 1 ≤ i.val
    · have hc := hneigh hi
      simp only [T, if_pos hi, Fin.val_zero, Matrix.add_apply, Matrix.single_apply_same,
        Matrix.single, Matrix.of_apply, Matrix.zero_apply, and_true, true_and,
        Matrix.single_apply, hval, hpar] at *
      split_ifs <;> simp_all <;> omega
    · have h0 : i.val = 0 := by omega
      have hiw : i ≠ w := by intro h; subst i; omega
      have hpa : ¬ (2 ≤ v.val ∧ heapColor (v.val / 2) = heapColor w.val ∧ i = parent n v) := by
        rintro ⟨hv2, _, hh⟩
        have hh' := congrArg Fin.val hh
        dsimp [parent] at hh'
        omega
      simp [T, hi, Matrix.single, hiw, Ne.symm hiw]
      split_ifs <;> simp_all [Matrix.single, parent] <;> omega
  · split_ifs <;> simp [hj, Ne.symm hj, Matrix.single]

private theorem transfer_row (n : ℕ) (v w : Fin (n + 2)) (hv : 1 ≤ v.val)
    (hw : 2 ≤ w.val) (hwp : w.val / 2 = v.val) :
    ⁅Matrix.single (0 : Fin (n + 2)) v (1 : ℂ), T n (heapColor v.val) (heapColor w.val)⁆ =
      Matrix.single (0 : Fin (n + 2)) w (1 : ℂ) +
        if 2 ≤ v.val ∧ heapColor (v.val / 2) = heapColor w.val
        then Matrix.single (0 : Fin (n + 2)) (parent n v) (1 : ℂ) else 0 := by
  have h := congrArg Matrix.transpose (transfer_column n v w hv hw hwp)
  split_ifs with hc <;>
    simpa [hc, Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul, T_transpose] using h

theorem anchored_units_mem (n : ℕ) (v : Fin (n + 2)) (hv : 1 ≤ v.val) :
    Matrix.single v (0 : Fin (n + 2)) (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) ∧
    Matrix.single (0 : Fin (n + 2)) v (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) := by
  have hh : ∀ k, ∀ v : Fin (n + 2), v.val = k → 1 ≤ v.val →
      Matrix.single v (0 : Fin (n + 2)) (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) ∧
      Matrix.single (0 : Fin (n + 2)) v (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hvk hv
      by_cases hv1 : v = 1
      · subst v
        simpa only [Fin.val_one, Nat.size_one, mul_one] using (anchor_units_mem n).symm
      · have hv2 : 2 ≤ v.val := by
          have hne : v.val ≠ 1 := by
            intro hvval
            apply hv1
            apply Fin.ext
            simpa only [Fin.val_one] using hvval
          omega
        let p := parent n v
        have hpp : 1 ≤ p.val := by dsimp [p, parent]; omega
        have hpv : p.val < v.val := Nat.div_lt_self (by omega) (by omega)
        have hp := ih p.val (by omega) p rfl hpp
        have hdv : Nat.size p.val + 1 = Nat.size v.val := depth_parent v.val hv2
        have hcolors : heapColor p.val ≠ heapColor v.val := Ne.symm (color_child_ne v.val hv2)
        have hTc := transfer_mem_eight n (heapColor v.val) (heapColor p.val)
          (color_lt p.val) (color_lt v.val) hcolors
        have hTr := transfer_mem_eight n (heapColor p.val) (heapColor v.val)
          (color_lt v.val) (color_lt p.val) (Ne.symm hcolors)
        have hLc : ⁅T n (heapColor v.val) (heapColor p.val),
            Matrix.single p (0 : Fin (n + 2)) (1 : ℂ)⁆ ∈
            rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) := by
          have h := rightSpan_bracket_mem (gen n) hTc hp.1
          have hb : 8 + 8 * Nat.size p.val = 8 * Nat.size v.val := by omega
          rw [hb] at h
          exact h
        have hLr : ⁅Matrix.single (0 : Fin (n + 2)) p (1 : ℂ),
            T n (heapColor p.val) (heapColor v.val)⁆ ∈
            rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) := by
          have h := rightSpan_bracket_mem (gen n) hp.2 hTr
          have hb : 8 * Nat.size p.val + 8 = 8 * Nat.size v.val := by omega
          rw [hb] at h
          exact h
        have hRc : (if 2 ≤ p.val ∧ heapColor (p.val / 2) = heapColor v.val
            then Matrix.single (parent n p) (0 : Fin (n + 2)) (1 : ℂ) else 0) ∈
            rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) := by
          split_ifs with h
          · have hqv : (parent n p).val < k := by
              exact (Nat.div_le_self p.val 2).trans_lt (hpv.trans_eq hvk)
            have hqp : 1 ≤ (parent n p).val := by dsimp [parent]; omega
            have hq := ih (parent n p).val hqv (parent n p) rfl hqp
            have hdp := depth_parent p.val h.1
            apply rightSpan_mono (gen n) (show 8 * Nat.size (parent n p).val ≤ 8 * Nat.size v.val by
              change 8 * Nat.size (p.val / 2) ≤ _
              omega) hq.1
          · exact Submodule.zero_mem _
        have hRr : (if 2 ≤ p.val ∧ heapColor (p.val / 2) = heapColor v.val
            then Matrix.single (0 : Fin (n + 2)) (parent n p) (1 : ℂ) else 0) ∈
            rightSpan (K := ℂ) (gen n) (8 * Nat.size v.val) := by
          split_ifs with h
          · have hqv : (parent n p).val < k := by
              exact (Nat.div_le_self p.val 2).trans_lt (hpv.trans_eq hvk)
            have hqp : 1 ≤ (parent n p).val := by dsimp [parent]; omega
            have hq := ih (parent n p).val hqv (parent n p) rfl hqp
            have hdp := depth_parent p.val h.1
            apply rightSpan_mono (gen n) (show 8 * Nat.size (parent n p).val ≤ 8 * Nat.size v.val by
              change 8 * Nat.size (p.val / 2) ≤ _
              omega) hq.2
          · exact Submodule.zero_mem _
        constructor
        · have h := Submodule.sub_mem _ hLc hRc
          rw [transfer_column n p v hpp hv2 rfl, add_sub_cancel_right] at h
          exact h
        · have h := Submodule.sub_mem _ hLr hRr
          rw [transfer_row n p v hpp hv2 rfl, add_sub_cancel_right] at h
          exact h
  exact hh v.val v rfl hv


open Matrix D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthConstruction
attribute [local instance] LieRing.ofAssociativeRing

private theorem anchored_bracket {N : ℕ} (v w o : Fin N) :
    ⁅Matrix.single v o (1 : ℂ), Matrix.single o w (1 : ℂ)⁆ =
      Matrix.single v w (1 : ℂ) - if w = v then Matrix.single o o (1 : ℂ) else 0 := by
  by_cases h : w = v
  · subst w
    simp [Ring.lie_def, Matrix.single_mul_single_same]
  · rw [Ring.lie_def, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (1 : ℂ) o w v h 1]
    simp [h]

private theorem trace_zero_mem_of_adjusted_units {N : ℕ} (o : Fin N)
    (W : Submodule ℂ ((Matrix (Fin N) (Fin N) ℂ)))
    (hu : ∀ i j, Matrix.single i j (1 : ℂ) -
      (if j = i then Matrix.single o o (1 : ℂ) else 0) ∈ W)
    (X : (Matrix (Fin N) (Fin N) ℂ)) (hX : Matrix.trace X = 0) : X ∈ W := by
  have hsum : (∑ i, ∑ j, (X i j) • (Matrix.single i j (1 : ℂ) -
      (if j = i then Matrix.single o o (1 : ℂ) else 0))) = X := by
    simp only [smul_sub, Finset.sum_sub_distrib, Matrix.smul_single, smul_eq_mul, mul_one]
    have hc : (∑ i, ∑ j, (X i j) •
        (if j = i then Matrix.single o o (1 : ℂ) else 0)) =
        Matrix.trace X • Matrix.single o o (1 : ℂ) := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Finset.sum_smul.symm
    rw [hc, hX, zero_smul, sub_zero, ← Matrix.matrix_eq_sum_single]
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact W.smul_mem _ (hu i j)

private theorem anchored_units_uniform (n : ℕ) (v : Fin (n + 2)) (hv : v ≠ 0) :
    Matrix.single v (0 : Fin (n + 2)) (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) (8 * (1 + Nat.log 2 (n + 1))) ∧
    Matrix.single (0 : Fin (n + 2)) v (1 : ℂ) ∈ rightSpan (K := ℂ) (gen n) (8 * (1 + Nat.log 2 (n + 1))) := by
  have hvp : 1 ≤ v.val := by
    have : v.val ≠ 0 := by
      intro h
      apply hv
      apply Fin.ext
      simpa only [Fin.val_zero] using h
    omega
  have hb : 8 * Nat.size v.val ≤ 8 * (1 + Nat.log 2 (n + 1)) := by
    have h := depth_bound (n + 2) v.val v.isLt
    simpa [] using Nat.mul_le_mul_left 8 h
  have hh := anchored_units_mem n v hvp
  exact ⟨rightSpan_mono (gen n) hb hh.1, rightSpan_mono (gen n) hb hh.2⟩

private theorem adjusted_units_mem (n : ℕ) (v w : Fin (n + 2)) :
    Matrix.single v w (1 : ℂ) -
      (if w = v then Matrix.single (0 : Fin (n + 2)) 0 (1 : ℂ) else 0) ∈
      rightSpan (K := ℂ) (gen n) (16 * (1 + Nat.log 2 (n + 1))) := by
  by_cases hv : v = 0
  · subst v
    by_cases hw : w = 0
    · simp [hw]
    · simpa [hw] using rightSpan_mono (gen n) (by omega : 8 * (1 + Nat.log 2 (n + 1)) ≤ 16 * (1 + Nat.log 2 (n + 1)))
        (anchored_units_uniform n w hw).2
  · by_cases hw : w = 0
    · subst w
      simpa [Ne.symm hv] using rightSpan_mono (gen n) (by omega : 8 * (1 + Nat.log 2 (n + 1)) ≤ 16 * (1 + Nat.log 2 (n + 1)))
        (anchored_units_uniform n v hv).1
    · rw [← anchored_bracket v w 0]
      have hh := rightSpan_bracket_mem (gen n)
        (anchored_units_uniform n v hv).1 (anchored_units_uniform n w hw).2
      have he : 8 * (1 + Nat.log 2 (n + 1)) + 8 * (1 + Nat.log 2 (n + 1)) = 16 * (1 + Nat.log 2 (n + 1)) := by omega
      rwa [he] at hh

private theorem traceless_full_span (n : ℕ) (X : (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)) (hX : Matrix.trace X = 0) :
    X ∈ rightSpan (K := ℂ) (gen n) (16 * (1 + Nat.log 2 (n + 1))) := by
  exact trace_zero_mem_of_adjusted_units 0 _ (adjusted_units_mem n) X hX


open Matrix D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthConstruction
attribute [local instance] LieRing.ofAssociativeRing

private theorem word_scaled {I K M : Type*} [Field K] [LieRing M] [LieAlgebra K M]
    (S : I → M) (c : K) (w : RightWord I) :
    w.rightWordEval (fun i => c • S i) = c ^ w.rightWordLength • w.rightWordEval S := by
  induction w with
  | single i => simp [rightWordEval, rightWordLength]
  | cons i w ih =>
    simp only [rightWordEval, ih, smul_lie, lie_smul, smul_smul, rightWordLength]
    simp [pow_succ', mul_comm]

private theorem rightSpan_le_scaled {I K M : Type*} [Field K] [LieRing M] [LieAlgebra K M]
    (S : I → M) (c : K) (hc : c ≠ 0) (L : ℕ) :
    rightSpan (K := K) S L ≤ rightSpan (K := K) (fun i => c • S i) L := by
  apply Submodule.span_le.mpr
  rintro X ⟨w, hw, rfl⟩
  have hh := Submodule.smul_mem (rightSpan (K := K) (fun i => c • S i) L)
    ((c ^ w.rightWordLength)⁻¹) (word_mem (fun i => c • S i) w L hw)
  rw [word_scaled, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul] at hh
  exact hh

private theorem A_hermitian (n : ℕ) : (A n).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff, centeredEnergy, meanEnergy]

private theorem A_trace (n : ℕ) : Matrix.trace (A n) = 0 := by
  simp only [A, Matrix.trace_diagonal, centeredEnergy, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, meanEnergy]
  have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hn' : (↑(n + 2) : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  push_cast
  rw [mul_div_cancel₀ _ hn, sub_self]

private theorem B_hermitian (n : ℕ) : (B n).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, B_apply, edge_symm j.val i.val]

private theorem B_trace (n : ℕ) : Matrix.trace (B n) = 0 := by
  simpa only [B] using
    (SimpleGraph.trace_adjMatrix (α := ℂ)
      (SimpleGraph.fromRel (fun i j : Fin (n + 2) => heapEdge i.val j.val)))

def iGen (n : ℕ) (i : Fin 2) : (Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) := Complex.I • gen n i

private theorem imaginary_hermitian_mem {N : ℕ} (X : (Matrix (Fin N) (Fin N) ℂ)) (hh : X.IsHermitian)
    (ht : Matrix.trace X = 0) : Complex.I • X ∈ suSet N := by
  constructor
  · rw [Matrix.conjTranspose_smul, hh.eq]
    simp
  · rw [Matrix.trace_smul, ht, smul_zero]

private theorem iGen_su (n : ℕ) (i : Fin 2) : iGen n i ∈ suSet (n + 2) := by
  fin_cases i
  · exact imaginary_hermitian_mem _ (A_hermitian n) (A_trace n)
  · exact imaginary_hermitian_mem _ (B_hermitian n) (B_trace n)

private theorem real_full_span (n : ℕ) :
    rightSpan (K := ℝ) (iGen n) (16 * (1 + Nat.log 2 (n + 1))) = suSet (n + 2) := by
  apply le_antisymm
  · exact rightSpan_real_le_su (iGen n) (iGen_su n) _
  · intro X hX
    apply rightSpan_complex_to_real (iGen n) (iGen_su n) _ X hX
    exact rightSpan_le_scaled (gen n) Complex.I Complex.I_ne_zero _ (traceless_full_span n X hX.2)


open D5.S3.Quantum.Algebra.GenericLieLengthFiltration D5.S3.Quantum.Algebra.GenericLieLengthConstruction
attribute [local instance] LieRing.ofAssociativeRing

instance suLieRing (n : ℕ) : LieRing (suSet n) := inferInstanceAs (LieRing (suLie n))
instance suLieAlgebra (n : ℕ) : LieAlgebra ℝ (suSet n) := inferInstanceAs (LieAlgebra ℝ (suLie n))


private theorem word_map {I K M N : Type*} [CommRing K] [LieRing M] [LieAlgebra K M]
    [LieRing N] [LieAlgebra K N] (f : M →ₗ⁅K⁆ N) (S : I → M) (w : RightWord I) :
    f (w.rightWordEval S) = w.rightWordEval (fun i => f (S i)) := by
  induction w with
  | single i => rfl
  | cons i w ih => simp only [rightWordEval, LieHom.map_lie, ih]

theorem rightSpan_map {I K M N : Type*} [CommRing K] [LieRing M] [LieAlgebra K M]
    [LieRing N] [LieAlgebra K N] (f : M →ₗ⁅K⁆ N) (S : I → M) (L : ℕ) :
    Submodule.map f.toLinearMap (rightSpan (K := K) S L) =
      rightSpan (K := K) (fun i => f (S i)) L := by
  rw [rightSpan, Submodule.map_span, rightSpan]
  congr 1
  ext X
  constructor
  · rintro ⟨Y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, (word_map f S w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.rightWordEval S, ⟨w, hw, rfl⟩, word_map f S w⟩

def compactPair (n : ℕ) (i : Fin 2) : suSet (n + 2) := ⟨iGen n i, iGen_su n i⟩

theorem compactPair_span_top (n : ℕ) :
    rightSpan (K := ℝ) (compactPair n) (16 * (1 + Nat.log 2 (n + 1))) = ⊤ := by
  apply Submodule.map_injective_of_injective (suSet (n + 2)).injective_subtype
  rw [Submodule.map_subtype_top]
  change Submodule.map (show suSet (n + 2) →ₗ⁅ℝ⁆ Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ
    from (suLie (n + 2)).incl).toLinearMap _ = _
  rw [rightSpan_map]
  exact real_full_span n


end
end D5.S3.Quantum.Algebra.GenericLieLengthConstruction
