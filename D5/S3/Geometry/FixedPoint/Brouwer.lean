/- GID: D5/S3/Geometry/FixedPoint/Brouwer
   generality: G
   mirror-B: D5/B/S3/Geometry/FixedPoint/Brouwer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: Shrinking lattice cells and outside-color estimates give a color-preserving subsequence and coordinatewise fixed point by continuity. -/
/- proof_shape: Brouwer: content
   admission_basis: escape-witness
   escape_witness: Shrinking lattice cells and outside-color estimates give a color-preserving subsequence and coordinatewise fixed point by continuity.
   Source: https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/Gametheory/Brouwer.lean
   No mathematical novelty claim. -/
/-
MIT License

Copyright (c) 2025 Math_XMUM

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import D5.S3.Geometry.FixedPoint.SimplexMesh
open Classical Finset Topology Filter
open D5.S3.Combinatorics.Scarf D5.S3.Combinatorics.Scarf.IndexedLOrder
noncomputable section
namespace D5.S3.Geometry.FixedPoint
variable (n : ℕ+) (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))
theorem Brouwer (hf : Continuous f) : ∃ x, f x = x := by
  classical
  let latticeOrders (n l : ℕ+) : IndexedLOrder (Fin n) (TT n l) :=
    ({ IST := fun i => by
        letI : IsStrictTotalOrder (TT n l) (TT.Ilt i) := {
          trichotomous := by
            intro a b h_ab h_ba
            unfold TT.Ilt at h_ab h_ba
            have h_eq :
                toLex (a.1 i, a) = toLex (b.1 i, b) :=
              le_antisymm (le_of_not_gt h_ba) (le_of_not_gt h_ab)
            have h_pair : (a.1 i, a) = (b.1 i, b) :=
              (EquivLike.injective (toLex : (Fin (l + 1) × TT n l) ≃
                Lex (Fin (l + 1) × TT n l))) h_eq
            exact congrArg Prod.snd h_pair
          irrefl := by
            intro a
            unfold TT.Ilt
            exact lt_irrefl _
          trans := by
            intro a b c h_ab h_bc
            unfold TT.Ilt at *
            exact lt_trans h_ab h_bc }
        exact linearOrderOfSTO (TT.Ilt i) } : IndexedLOrder (Fin n) (TT n l))
  let toSimplex {n l : ℕ+} (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x.1 i / l, by
    rw [stdSimplex]
    constructor
    · intro
      apply div_nonneg <;> simp
    ·
      rw [<-Finset.sum_div, div_eq_one_iff_eq]
      · exact_mod_cast x.2
      · exact Iff.mpr Nat.cast_ne_zero (PNat.ne_zero l)
    ⟩
  have size_bound_in (n l : ℕ+) (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : (latticeOrders n l).isDominant σ C):
      ∀ x ∈ σ, ∀ y ∈ σ, ∀ i : Fin n, abs ((x.1 i : ℤ) - (y.1 i : ℤ)) < 2 * (n + 1)
      := by
    by_cases hσ : σ.Nonempty
    · intro x hx y hy i
      let m k := (σ.image (fun z => (z.1 k : ℕ))).min' (hσ.image _)
      let m' i := if h_i : i ∈ C then m i else 0
      have h_le_l_sub_sum : (l : ℕ) - ∑ k ∈ C, m k < C.card := by
        have h_key : l < ∑ k ∈ C, m k + C.card := size_bound_key n l σ C h hσ
        have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
          rcases hσ with ⟨x, hx⟩
          have h_m_le : ∀ k ∈ C, m k ≤ (x.1 k : ℕ) := fun k _ =>
            Finset.min'_le (σ.image (fun z => (z.1 k : ℕ))) (x.1 k : ℕ) (Finset.mem_image_of_mem (fun z => (z.1 k : ℕ)) hx)
          calc
            ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x.1 k : ℕ) := Finset.sum_le_sum h_m_le
            _ ≤ ∑ k, (x.1 k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
            _ = l := x.2
        rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
        exact h_key
      have h_bound : ∀ z ∈ σ, (z.1 i : ℕ) - m' i < C.card := by
        intro z hz
        by_cases hi_in_C : i ∈ C
        · simp [m', hi_in_C]
          have h_mi_le_zi : m i ≤ (z.1 i : ℕ) := by
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          have h_zi_le_sum : (z.1 i : ℕ) ≤ ∑ k ∈ C, (z.1 k : ℕ) :=
            Finset.single_le_sum (fun k _ => Nat.zero_le (z.1 k : ℕ)) hi_in_C
          have h_sum_z_le_l : ∑ k ∈ C, (z.1 k : ℕ) ≤ l := by
            calc ∑ k ∈ C, (z.1 k : ℕ) ≤ ∑ k, (z.1 k : ℕ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
            _ = l := z.2
          have h_diff_bound : (z.1 i : ℕ) - m i ≤ l - ∑ k ∈ C, m k := by
            calc
            (z.1 i : ℕ) - m i ≤ ∑ k ∈ C, ((z.1 k : ℕ) - m k) :=
              Finset.single_le_sum (fun k _ => Nat.zero_le ((z.1 k : ℕ) - m k)) hi_in_C
            _ = (∑ k ∈ C, (z.1 k : ℕ)) - (∑ k ∈ C, m k) := by
              rw [Finset.sum_tsub_distrib]
              intro k hk
              apply Finset.min'_le
              apply Finset.mem_image_of_mem
              exact hz
            _ ≤ l - ∑ k ∈ C, m k := by
              apply Nat.sub_le_sub_right
              calc
                ∑ k ∈ C, (z.1 k : ℕ) ≤ ∑ k, (z.1 k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
                _ = l := z.2
          exact lt_of_le_of_lt h_diff_bound h_le_l_sub_sum
        · simp [m', hi_in_C]
          have h_sum_le : (z.1 i : ℕ) + ∑ k ∈ C, (z.1 k : ℕ) ≤ l := by
            calc
              (z.1 i : ℕ) + ∑ k ∈ C, (z.1 k : ℕ) = ∑ k ∈ insert i C, (z.1 k : ℕ) := by
                rw [Finset.sum_insert hi_in_C]
              _ ≤ ∑ k, (z.1 k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
              _ = l := z.2
          have h_le_sub : (z.1 i : ℕ) ≤ l - ∑ k ∈ C, (z.1 k : ℕ) := Nat.le_sub_of_add_le h_sum_le
          have h_m_le_z : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (z.1 k : ℕ) := by
            apply Finset.sum_le_sum
            intro k hk
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          have h_sub_le_sub : l - ∑ k ∈ C, (z.1 k : ℕ) ≤ l - ∑ k ∈ C, m k :=
            Nat.sub_le_sub_left h_m_le_z l
          exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
      have h_nonneg : ∀ z ∈ σ, 0 ≤ (z.1 i : ℤ) - (m' i : ℤ) := by
        intro z hz
        by_cases hi_in_C : i ∈ C
        · simp [m', hi_in_C]
          have h_min_le : m i ≤ ↑(z.1 i) := by
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          exact_mod_cast h_min_le
        · simp [m', hi_in_C]
      have h_abs_lt_2_card : abs ((x.1 i : ℤ) - (y.1 i : ℤ)) < 2 * (C.card : ℤ) := by
        have h_bound_int : ∀ z ∈ σ, (z.1 i : ℤ) - (m' i : ℤ) < C.card := by
          intro z hz
          have := h_bound z hz
          simp only [m'] at this ⊢
          split_ifs at this ⊢ with h_case
          · have : (z.1 i : ℕ) - m i < C.card := this
            simp
            have h_le : m i ≤ (z.1 i : ℕ) := by
              apply Finset.min'_le
              apply Finset.mem_image_of_mem
              exact hz
            omega
          · simp only [Int.ofNat_zero, sub_zero]
            exact Int.ofNat_lt.mpr this
        calc
          abs ((x.1 i : ℤ) - (y.1 i : ℤ)) = abs (((x.1 i : ℤ) - (m' i : ℤ)) - ((y.1 i : ℤ) - (m' i : ℤ))) := by rw [sub_sub_sub_cancel_right]
          _ ≤ abs ((x.1 i : ℤ) - (m' i : ℤ)) + abs ((y.1 i : ℤ) - (m' i : ℤ)) := abs_sub _ _
          _ = ((x.1 i : ℤ) - (m' i : ℤ)) + ((y.1 i : ℤ) - (m' i : ℤ)) := by
            rw [abs_of_nonneg (h_nonneg x hx), abs_of_nonneg (h_nonneg y hy)]
          _ < (C.card : ℤ) + (C.card : ℤ) := by
            apply add_lt_add (h_bound_int x hx) (h_bound_int y hy)
          _ = 2 * (C.card : ℤ) := by rw [two_mul]
      have h_card_le_n : C.card ≤ n :=
        calc
          C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
          _ = n := by simp
      apply lt_trans h_abs_lt_2_card
      have : (2 * (C.card : ℤ)) < 2 * (n + 1 : ℤ) := by
        linarith [Int.ofNat_le.mpr h_card_le_n]
      exact this
    · intro x hx y hy i
      exfalso
      exact hσ ⟨x, hx⟩
  have size_bound_out (n l : ℕ+) (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : (latticeOrders n l).isDominant σ C):
      ∀ x ∈ σ, ∀ i ∉ C, (x.1 i : ℤ) < n + 1
      := by
    by_cases hσ : σ.Nonempty
    · intro x hx i hi_not_C
      let m k := (σ.image (fun z => (z.1 k : ℕ))).min' (hσ.image _)
      have h_le_l_sub_sum : l - ∑ k ∈ C, m k < C.card := by
        have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
          rcases hσ with ⟨x, hx⟩
          have h_m_le : ∀ k ∈ C, m k ≤ (x.1 k : ℕ) := fun k _ =>
            Finset.min'_le (σ.image (fun z => (z.1 k : ℕ))) (x.1 k : ℕ) (Finset.mem_image_of_mem (fun z => (z.1 k : ℕ)) hx)
          calc
            ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x.1 k : ℕ) := Finset.sum_le_sum h_m_le
            _ ≤ ∑ k, (x.1 k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
            _ = l := x.2
        rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
        exact size_bound_key n l σ C h hσ
      have h_bound : (x.1 i : ℕ) < C.card := by
        have h_sum_le : (x.1 i : ℕ) + ∑ k ∈ C, (x.1 k : ℕ) ≤ l := by
          calc
            (x.1 i : ℕ) + ∑ k ∈ C, (x.1 k : ℕ) = ∑ k ∈ insert i C, (x.1 k : ℕ) := by
              rw [Finset.sum_insert hi_not_C]
            _ ≤ ∑ k, (x.1 k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
            _ = l := x.2
        have h_le_sub : (x.1 i : ℕ) ≤ l - ∑ k ∈ C, (x.1 k : ℕ) := Nat.le_sub_of_add_le h_sum_le
        have h_m_le_x : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x.1 k : ℕ) := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hx
        have h_sub_le_sub : l - ∑ k ∈ C, (x.1 k : ℕ) ≤ l - ∑ k ∈ C, m k :=
          Nat.sub_le_sub_left h_m_le_x l
        exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
      have h_card_le_n : C.card ≤ n := by
        calc
          C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
          _ = n := by simp [Fintype.card_fin]
      have h_lt_n : (x.1 i : ℤ) < ↑n := by
        apply lt_of_lt_of_le
        · exact Int.ofNat_lt.mpr h_bound
        · exact Int.ofNat_le.mpr h_card_le_n
      linarith
    · intro x hx
      exfalso
      exact hσ ⟨x, hx⟩
  have upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by
    by_contra h
    push Not at h
    have sum_x_eq_1 := x.2.2
    have sum_y_eq_1 := y.2.2
    have sum_lt : Finset.sum Finset.univ y.1 < Finset.sum Finset.univ x.1 := by
      apply Finset.sum_lt_sum_of_nonempty
      . exact Finset.univ_nonempty
      . intro i _
        have : ¬ (x.1 i ≤ y.1 i) := by
          intro hle
          exact @IsEmpty.false _ h ⟨i, hle⟩
        exact lt_of_not_ge this
    rw [sum_y_eq_1, sum_x_eq_1] at sum_lt
    exact (lt_irrefl 1 sum_lt).elim
  let pick (x y : stdSimplex ℝ (Fin n)) := Classical.choice (upidx x y)
  let Fcolor (l : ℕ+) (x : TT n l) : Fin n :=
    (pick (toSimplex x) (f (toSimplex x))).val
  have lattice_finite (l : ℕ+) : Finite (TT n l) := by
    letI : Finite (Πₗ (_ : Fin n), Fin (l + 1)) :=
      (Equiv.finite_iff toLex).1 Pi.finite
    exact Subtype.finite
  let room_seq (l' : ℕ) :=
    let l : ℕ+ := ⟨l' + 1, Nat.zero_lt_succ _⟩
    letI : Finite (TT n l) := lattice_finite l
    letI : Fintype (TT n l) := Fintype.ofFinite _
    letI : Inhabited (TT n l) := {
      default :=
        ⟨ fun i => if i = 0 then Fin.last l else 0,  by
          change ∑ i, ((if i = 0 then Fin.last l else 0 : Fin (l + 1)) : ℕ) = l
          rw [Finset.sum_eq_single (0 : Fin n)]
          · simp
          · intro b _ hb; simp [hb]
          · simp [Fin.val_last] ⟩ }
    Classical.choice ((latticeOrders n l).Scarf (Fcolor l)).to_subtype
  have room_nonempty (l' : ℕ) : ((room_seq l').1.1).Nonempty := by
    have hc := (Finset.mem_filter.1 (room_seq l').2).2
    have hC : ((room_seq l').1.2).Nonempty := by
      let l0 : ℕ+ := ⟨l' + 1, Nat.zero_lt_succ _⟩
      let x0 : TT n l0 := ⟨fun k => if k = 0 then Fin.last l0 else 0, by
        change ∑ k, ((if k = 0 then Fin.last l0 else 0 : Fin (l0 + 1)) : ℕ) = l0
        rw [Finset.sum_eq_single (0 : Fin n)]
        · simp
        · intro b _ hb
          simp [hb]
        · simp [Fin.val_last]⟩
      obtain ⟨j, hj⟩ := hc.1 x0
      exact ⟨j, hj.1⟩
    obtain ⟨j, hj⟩ := hC
    have hjimage : j ∈ ((room_seq l').1.1).image (Fcolor ⟨l' + 1, Nat.succ_pos _⟩) := by
      rw [hc.2]; exact hj
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hjimage
    exact ⟨x, hx⟩
  let room_point_seq (l' : ℕ) := Classical.choice (room_nonempty l').to_subtype
  let room_point_std_seq (l' : ℕ) : stdSimplex ℝ (Fin n) :=
    toSimplex (room_point_seq l').val
  have room_point_seq_mem (l' : ℕ) : (room_point_seq l').val ∈ (room_seq l').1.1 :=
    (room_point_seq l').property
  obtain ⟨C₀, hC₀⟩ := Finite.exists_infinite_fiber (fun k : ℕ => (room_seq k).1.2)
  have arbitrarily_late : ∀ N, ∃ k > N, (room_seq k).1.2 = C₀ := by
    have hinf : Set.Infinite {k : ℕ | (room_seq k).1.2 = C₀} :=
      Set.infinite_coe_iff.mp hC₀
    intro N
    by_contra! h
    exact hinf ((Set.finite_le_nat N).subset (fun k hk =>
      le_of_not_gt (fun hNk => h k hNk hk)))
  obtain ⟨g, hg, hconstant⟩ := Nat.exists_strictMono_subsequence arbitrarily_late
  let gpkg : {(a, g) : Finset (Fin n) × (ℕ ↪o ℕ) |
      ∀ k, (room_seq (g k)).1.2 = a} :=
    ⟨(C₀, OrderEmbedding.ofStrictMono g hg), hconstant⟩
  let g1 : ℕ ↪o ℕ := gpkg.val.2
  obtain ⟨z₀, _, φ₀, hφ₀, hlim₀⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (stdSimplex ℝ (Fin n)))).tendsto_subseq
      (fun k => Set.mem_univ (room_point_std_seq (g1 k)))
  let hpkg : {(z, h) : stdSimplex ℝ (Fin n) × (ℕ → ℕ) |
      StrictMono h ∧ Tendsto (room_point_std_seq ∘ g1 ∘ h) atTop (𝓝 z)} :=
    ⟨(z₀, φ₀), hφ₀, hlim₀⟩
  have dominant_coords_tend_to_zero (C : Finset (Fin n)) (g : ℕ ↪o ℕ) (h_const : ∀ l', (room_seq (g l')).1.2 = C) :
    ∀ i ∉ C, Filter.Tendsto (fun l' => (room_point_std_seq (g l')).1 i) Filter.atTop (𝓝 0) := by
    intro i hiC
    have h_tendsto_bound : Filter.Tendsto (fun l' => ((n : ℝ) + 1) / ((g l' : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      have h_denom_tendsto : Filter.Tendsto (fun l' => (g l' : ℝ) + 1) Filter.atTop Filter.atTop := by
        have g_tendsto : Filter.Tendsto (fun l' => g l') Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop_atTop.mpr
          intro b
          use b
          intro l' hl'
          exact le_trans hl' (StrictMono.id_le g.strictMono l')
        have cast_tendsto : Filter.Tendsto (fun l' => (g l' : ℝ)) Filter.atTop Filter.atTop :=
          Filter.Tendsto.comp tendsto_natCast_atTop_atTop g_tendsto
        exact Tendsto.atTop_add cast_tendsto (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
      have : Tendsto (fun l' => ((n : ℝ) + 1) / ((g l' : ℝ) + 1)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds h_denom_tendsto
      exact this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) h_tendsto_bound
    · intro l'
      exact (room_point_std_seq (g l')).2.1 i
    · intro l'
      let l_pnat : PNat := ⟨g l' + 1, Nat.succ_pos _⟩
      let rs := room_seq (g l')
      let σ := rs.1.1
      let C_l := rs.1.2
      have h_C_l : C_l = C := h_const l'
      have hiC_l : i ∉ C_l := h_C_l ▸ hiC
      let x := (room_point_seq (g l')).val
      let colorful_proof := (Finset.mem_filter.mp rs.2).2
      have hx_mem : x ∈ σ := room_point_seq_mem (g l')
      have h_dom : (latticeOrders n l_pnat).isDominant σ C_l := colorful_proof.1
      have h_bound := size_bound_out n l_pnat σ C_l h_dom x hx_mem i hiC_l
      simp only [room_point_std_seq, toSimplex, Subtype.coe_mk]
      have h_eq : (↑l_pnat : ℝ) = ↑(g l') + 1 := by simp [l_pnat, PNat.mk_coe]
      rw [h_eq]
      rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < ↑(g l') + 1)]
      have h_bound_real : ((x.1 i : ℕ) : ℝ) < (↑n + 1 : ℝ) := by
        exact_mod_cast Nat.lt_succ_of_le (Int.ofNat_le.mp (Int.le_of_lt_add_one h_bound))
      exact le_of_lt h_bound_real
  have tendsto_diam_to_zero :
    Tendsto
      (fun k =>
        Metric.diam
          ((((room_seq (g1 ((hpkg).1.2 k))).1.1.image (fun x => toSimplex x)) :
            Set (stdSimplex ℝ (Fin n)))))
      atTop (𝓝 0) := by
    let l k := g1 ((hpkg).1.2 k)
    let σ k := (room_seq (l k)).1.1
    let projected_σ k := (σ k).image (fun x => toSimplex x)
    have h_diam_bounded : ∃ (C : ℝ), ∀ k, Metric.diam ((projected_σ k : Set (stdSimplex ℝ (Fin n)))) ≤ C / (l k + 1) := by
      use 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1)
      intro k
      let l_pnat : PNat := ⟨l k + 1, Nat.succ_pos _⟩
      let rs := room_seq (l k)
      let C_k := rs.1.2
      have h_dom : (latticeOrders n l_pnat).isDominant (σ k) C_k := (Finset.mem_filter.mp rs.2).2.1
      have h_coord_bound : ∀ x ∈ (σ k), ∀ y ∈ (σ k), ∀ i : Fin n,
          abs (((toSimplex x).1 i : ℝ) - ((toSimplex y).1 i : ℝ)) < 2 * ((n : ℝ) + 1) / (l k + 1) := by
        intro x hx y hy i
        have h_bound_int := size_bound_in n l_pnat (σ k) C_k h_dom x hx y hy i
        simp only [toSimplex]
        rw [← sub_div]
        rw [abs_div]
        have h_pos : (0 : ℝ) < l_pnat := by positivity
        rw [abs_of_pos h_pos]
        have h_eq : (l_pnat : ℝ) = l k + 1 := by simp [l_pnat, PNat.mk_coe]
        rw [h_eq]
        rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
        exact_mod_cast h_bound_int
      have h_dist_bound : ∀ x ∈ (σ k), ∀ y ∈ (σ k),
          dist (toSimplex x) (toSimplex y) ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) / (l k + 1) := by
        intro x hx y hy
        have h_coord_diff_le : ∀ i, |(toSimplex x).1 i - (toSimplex y).1 i| ≤ 2 * (↑n + 1) / (↑(l k) + 1) :=
          fun i => le_of_lt (h_coord_bound x hx y hy i)
        calc dist (toSimplex x) (toSimplex y)
          = ‖(toSimplex x).1 - (toSimplex y).1‖ := rfl
        _ ≤ 2 * (↑n + 1) / (l k + 1) := by
            rw [pi_norm_le_iff_of_nonneg (by positivity)]
            exact h_coord_diff_le
        _ ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) / (l k + 1) := by
            rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < l k + 1)]
            have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
              apply Real.one_le_sqrt.mpr
              norm_cast
              exact Nat.succ_le_of_lt n.2
            calc
              2 * ((n : ℝ) + 1) = 1 * (2 * ((n : ℝ) + 1)) := by ring
              _ ≤ Real.sqrt (n : ℝ) * (2 * ((n : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_right hsqrt (by positivity)
              _ = 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) := by ring
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      intro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
      exact h_dist_bound x' hx' y' hy'
    rcases h_diam_bounded with ⟨C, hC_bound⟩
    have h_l_tends_to_inf : Tendsto (fun k => (l k : ℝ) + 1) atTop atTop := by
      have h_l_mono : StrictMono l := (g1).strictMono.comp (hpkg).2.1
      have h_l_tends_nat : Tendsto l atTop atTop := h_l_mono.tendsto_atTop
      have h_l_tends_real : Tendsto (fun k => (l k : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp h_l_tends_nat
      exact Tendsto.atTop_add h_l_tends_real tendsto_const_nhds
    have h_C_div_l_tends_to_zero : Tendsto (fun k => C / (l k + 1)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop h_l_tends_to_inf
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun _ => (0:ℝ)) atTop (𝓝 0)) h_C_div_l_tends_to_zero (fun _ => Metric.diam_nonneg) hC_bound
  have f_coords_ge_z_coords :
    ∀ i ∈ (gpkg).1.1, (f (hpkg).1.1).1 i ≥ ((hpkg).1.1).1 i := by
        let z := (hpkg).1.1
        let C := (gpkg).1.1
        let φ := (hpkg).1.2
        have convergence_to_z : Filter.Tendsto (room_point_std_seq ∘ g1 ∘ φ) Filter.atTop (𝓝 z) := by
          exact (hpkg).2.2
        have constant_color_set : ∀ l', (room_seq (g1 l')).1.2 = C := by
          exact (gpkg).2
        intro idx h_idx_C
        have h_exists_point : ∀ l', ∃ y,
          y ∈ (room_seq (g1 l')).1.1 ∧
          (let l_pnat : PNat := ⟨(g1) l' + 1, by simp⟩; Fcolor l_pnat y) = idx := by
          intro l'
          let l_pnat : PNat := ⟨(g1) l' + 1, by simp⟩
          let rs := room_seq (g1 l')
          let σ := rs.1.1
          let C_l := rs.1.2
          have h_C_l : C_l = C := constant_color_set l'
          let colorful_proof := (Finset.mem_filter.mp rs.2).2
          have h_image_eq : σ.image (Fcolor l_pnat) = C_l := colorful_proof.2
          have h_idx_in_C_l : idx ∈ C_l := h_C_l ▸ h_idx_C
          have h_idx_in_image : idx ∈ σ.image (Fcolor l_pnat) := by
            rw [h_image_eq]; exact h_idx_in_C_l
          rw [Finset.mem_image] at h_idx_in_image
          obtain ⟨y, hy_in_σ, hy_color⟩ := h_idx_in_image
          use y
        let y_seq := fun l' => toSimplex (h_exists_point l').choose
        have y_seq_spec : ∀ l',
          (h_exists_point l').choose ∈ (room_seq (g1 l')).1.1 ∧
          (let l_pnat : PNat := ⟨(g1) l' + 1, by simp⟩; Fcolor l_pnat (h_exists_point l').choose) = idx := by
          intro l'
          exact (h_exists_point l').choose_spec
        have h_ineq : ∀ l', (f (y_seq l')).1 idx ≥ (y_seq l').1 idx := by
          intro l'
          let chosen_point := (h_exists_point l').choose
          let chosen_std_point := toSimplex chosen_point
          change chosen_std_point.1 idx ≤ (f chosen_std_point).1 idx
          have h_spec := y_seq_spec l'
          have h_color : (let l_pnat : PNat := ⟨(g1) l' + 1, by simp⟩; Fcolor l_pnat chosen_point) = idx := h_spec.2
          let l_pnat : PNat := ⟨(g1) l' + 1, by simp⟩
          change (pick chosen_std_point (f chosen_std_point)).val = idx at h_color
          have h_mem := (pick chosen_std_point (f chosen_std_point)).property
          change chosen_std_point.1 (pick chosen_std_point (f chosen_std_point)).val ≤
            (f chosen_std_point).1 (pick chosen_std_point (f chosen_std_point)).val at h_mem
          simpa only [h_color] using h_mem
        have y_seq_φ_converges_to_z : Filter.Tendsto (y_seq ∘ φ) Filter.atTop (𝓝 z) := by
          have h_dist_tends_to_zero : Filter.Tendsto (fun k => dist (y_seq (φ k)) (room_point_std_seq (g1 (φ k)))) Filter.atTop (𝓝 0) := by
            have h_bound : ∀ k, dist (y_seq (φ k)) (room_point_std_seq (g1 (φ k))) ≤
                  Metric.diam ((((room_seq (g1 (φ k))).1.1.image (fun x => toSimplex x)) : Set (stdSimplex ℝ (Fin n)))) := by
              intro k
              apply Metric.dist_le_diam_of_mem
              · exact Set.Finite.isBounded (Finset.finite_toSet _)
              · exact Finset.mem_image_of_mem toSimplex (y_seq_spec (φ k)).1
              · exact Finset.mem_image_of_mem toSimplex (room_point_seq_mem (g1 (φ k)))
            have h_diam_tendsto : Tendsto (fun k => Metric.diam ((((room_seq (g1 (φ k))).1.1.image toSimplex) : Set (stdSimplex ℝ (Fin n))))) atTop (𝓝 0) := by
              exact tendsto_diam_to_zero
            exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_diam_tendsto
              (Eventually.of_forall (fun _ => dist_nonneg)) (Eventually.of_forall h_bound)
          rw [Metric.tendsto_nhds]
          intro ε hε
          have h1 := (Metric.tendsto_nhds.1 convergence_to_z) (ε / 2) (half_pos hε)
          have h2 := (Metric.tendsto_nhds.1 h_dist_tends_to_zero) (ε / 2) (half_pos hε)
          apply (h1.and h2).mono
          intro k ⟨hk1, hk2⟩
          calc dist (y_seq (φ k)) z
            ≤ dist (y_seq (φ k)) (room_point_std_seq (g1 (φ k)))
              + dist (room_point_std_seq (g1 (φ k))) z := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add (by simp at hk2; exact hk2) hk1
          _ = ε := add_halves ε
        have f_y_seq_φ_converges_to_f_z : Filter.Tendsto (f ∘ y_seq ∘ φ) Filter.atTop (𝓝 (f z)) := by
          exact hf.continuousAt.tendsto.comp y_seq_φ_converges_to_z
        have f_y_seq_φ_coord_converges : Filter.Tendsto (fun l' => (f (y_seq (φ l'))).1 idx) Filter.atTop (𝓝 ((f z).1 idx)) := by
          have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 idx) :=
            Continuous.comp (continuous_apply idx) continuous_subtype_val
          exact h_continuous.continuousAt.tendsto.comp f_y_seq_φ_converges_to_f_z
        have y_seq_φ_coord_converges : Filter.Tendsto (fun l' => (y_seq (φ l')).1 idx) Filter.atTop (𝓝 (z.1 idx)) := by
          have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 idx) :=
            Continuous.comp (continuous_apply idx) continuous_subtype_val
          exact h_continuous.continuousAt.tendsto.comp y_seq_φ_converges_to_z
        exact le_of_tendsto_of_tendsto y_seq_φ_coord_converges f_y_seq_φ_coord_converges (Eventually.of_forall (fun l' => h_ineq (φ l')))
  let z := (hpkg).1.1
  let C := (gpkg).1.1
  let φ := (hpkg).1.2
  use z
  
  have convergence_to_z : Filter.Tendsto (room_point_std_seq ∘ g1 ∘ φ) Filter.atTop (𝓝 z) :=
    (hpkg).2.2
  have constant_color_set : ∀ l', (room_seq (g1 l')).1.2 = C :=
    (gpkg).2
  have coords_outside_C_zero : ∀ i_1 ∉ C, z.1 i_1 = 0 := by
    intro i_1 hi_not_C
    have tendsto_zero : Filter.Tendsto (fun l' => (room_point_std_seq (g1 l')).1 i_1) Filter.atTop (𝓝 0) :=
      dominant_coords_tend_to_zero C (g1) constant_color_set i_1 hi_not_C
    have h_tendsto_coord_z : Tendsto (fun k => (room_point_std_seq (g1 (φ k))).1 i_1) atTop (𝓝 (z.1 i_1)) := by
      have h_continuous : Continuous (fun x : stdSimplex ℝ (Fin n) => x.1 i_1) :=
        Continuous.comp (continuous_apply i_1) continuous_subtype_val
      exact h_continuous.continuousAt.tendsto.comp convergence_to_z
    have tendsto_zero_subseq : Tendsto (fun k => (room_point_std_seq (g1 (φ k))).1 i_1) atTop (𝓝 0) :=
      (dominant_coords_tend_to_zero C (g1) constant_color_set i_1 hi_not_C).comp (hpkg).2.1.tendsto_atTop
    exact tendsto_nhds_unique h_tendsto_coord_z tendsto_zero_subseq
  have sum_coords_in_C_eq_one : ∑ i_1 ∈ C, z.1 i_1 = 1 := by
    have total_sum_eq_one : ∑ i, z.1 i = 1 := z.2.2
    have split_sum : ∑ i, z.1 i = ∑ i ∈ C, z.1 i + ∑ i ∈ Cᶜ, z.1 i :=
      (Finset.sum_add_sum_compl C (z.1)).symm
    have compl_sum_zero : ∑ i ∈ Cᶜ, z.1 i = 0 := by
      apply Finset.sum_eq_zero
      intro i_1 hi
      exact coords_outside_C_zero i_1 (Finset.mem_compl.mp hi)
    rw [split_sum, compl_sum_zero, add_zero] at total_sum_eq_one
    exact total_sum_eq_one
  
  have sum_f_coords_ge_one : ∑ i_1 ∈ C, (f z).1 i_1 ≥ 1 := by
    calc ∑ i_1 ∈ C, (f z).1 i_1
        ≥ ∑ i_1 ∈ C, z.1 i_1 := Finset.sum_le_sum fun i_1 hi => f_coords_ge_z_coords i_1 hi
      _ = 1 := sum_coords_in_C_eq_one
  have f_coords_outside_C_zero : ∀ i_1 ∉ C, (f z).1 i_1 = 0 := by
    intro i_1 hi_not_C
    have total_sum_f : ∑ i, (f z).1 i = 1 := (f z).2.2
    have sum_f_C_eq_one : ∑ i_2 ∈ C, (f z).1 i_2 = 1 := by
      have : ∑ i_2 ∈ C, (f z).1 i_2 ≤ 1 := by
        calc ∑ i_2 ∈ C, (f z).1 i_2
          ≤ ∑ i, (f z).1 i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun i_2 _ _ => (f z).2.1 i_2)
          _ = 1 := total_sum_f
      exact le_antisymm this sum_f_coords_ge_one
    have compl_sum_zero : ∑ i_2 ∈ Cᶜ, (f z).1 i_2 = 0 := by
      have split_sum : ∑ i, (f z).1 i = ∑ i ∈ C, (f z).1 i + ∑ i ∈ Cᶜ, (f z).1 i :=
        (Finset.sum_add_sum_compl C ((f z).1)).symm
      rw [total_sum_f, sum_f_C_eq_one] at split_sum
      linarith
    have hi_in_compl : i_1 ∈ Cᶜ := Finset.mem_compl.mpr hi_not_C
    have h_nonneg : (f z).1 i_1 ≥ 0 := (f z).2.1 i_1
    have h_le_sum : (f z).1 i_1 ≤ ∑ j ∈ Cᶜ, (f z).1 j := Finset.single_le_sum (fun j _ => (f z).2.1 j) hi_in_compl
    rw [compl_sum_zero] at h_le_sum
    exact le_antisymm h_le_sum h_nonneg
  have f_coords_eq_z_coords : ∀ i_1 ∈ C, (f z).1 i_1 = z.1 i_1 := by
    intro i_1 hi_C
    have h_sum_f_C_eq_one : ∑ i_2 ∈ C, (f z).1 i_2 = 1 := by
      have total_sum_f : ∑ i, (f z).1 i = 1 := (f z).2.2
      have : ∑ i_2 ∈ C, (f z).1 i_2 ≤ 1 := by
        calc
          ∑ i_2 ∈ C, (f z).1 i_2 ≤ ∑ i, (f z).1 i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (fun i_2 _ _ => (f z).2.1 i_2)
          _ = 1 := total_sum_f
      exact le_antisymm this (sum_f_coords_ge_one)
    have h_sum_eq : ∑ i_2 ∈ C, (f z).1 i_2 = ∑ i_2 ∈ C, z.1 i_2 := by
      rw [h_sum_f_C_eq_one, sum_coords_in_C_eq_one]
    exact (((Finset.sum_eq_sum_iff_of_le fun i_2 hi => f_coords_ge_z_coords i_2 hi).mp h_sum_eq.symm) i_1 hi_C).symm
  ext i_1
  by_cases hi : i_1 ∈ C
  · exact f_coords_eq_z_coords i_1 hi
  · change (f z).1 i_1 = z.1 i_1
    rw [f_coords_outside_C_zero i_1 hi, coords_outside_C_zero i_1 hi]
end D5.S3.Geometry.FixedPoint
