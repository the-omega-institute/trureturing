/- GID: D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The max-minus-min statistic is zero-sum on every literal interval-closed rectangle rowmotion orbit. -/

import D5.S3.Combinatorics.Geometry.RectangularCorner
import D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

open D5.S3.Combinatorics.Geometry.RectangularCorner
namespace D5.S3.Combinatorics.Geometry.RectangleRowmotionHomomesy
open D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open scoped BigOperators symmDiff

noncomputable def literalOrbit {m n N : ℕ} (e : Fin N ≃ Point m n)
    (I : Set (Point m n)) : Finset (Set (Point m n)) := by
  classical
  exact Finset.univ.filter (fun S => ∃ k : ℕ, (fun T => trace (P := Point m n) e T N)^[k] I = S)

noncomputable def maxMinusMin {m n : ℕ} (I : Set (Point m n)) : ℤ := by
  classical
  exact ((Finset.univ.filter (fun a => Maximal (· ∈ I) a)).card : ℤ) -
    ((Finset.univ.filter (fun u => Minimal (· ∈ I) u)).card : ℤ)

theorem result {m n N : ℕ} (_hm : 0 < m) (_hn : 0 < n)
    (e : Fin N ≃ Point m n) (he : ReverseExtension e)
    (I : Set (Point m n)) (hI : I.OrdConnected) :
    ∑ S ∈ literalOrbit e I, maxMinusMin S = 0 := by
  classical
  let H : Set (Point m n) → ℕ := fun S => (Finset.univ.filter (fun z : (Point m n) × (Point m n) =>
    Maximal (· ∈ (lowerClosure S : Set (Point m n)) \ S) z.1 ∧ Maximal (· ∈ S) z.2 ∧
      z.1.1 < z.2.1 ∧ z.1.2 < z.2.2)).card
  let Q : Set (Point m n) → ℕ := fun S => (Finset.univ.filter (fun z : (Point m n) × (Point m n) =>
    Minimal (· ∈ S) z.1 ∧ Minimal (· ∈ (upperClosure S : Set (Point m n)) \ S) z.2 ∧
      z.1.1 < z.2.1 ∧ z.1.2 < z.2.2)).card
  let E : Set (Point m n) → ℕ := fun S => (Finset.univ.filter (fun z : (Point m n) × (Point m n) =>
    Minimal (· ∈ S) z.1 ∧ Maximal (· ∈ S) z.2 ∧ z.1 ≤ z.2)).card
  let A : Set (Point m n) → ℕ := fun S => (Finset.univ.filter (fun a => Maximal (· ∈ S) a)).card
  let M : Set (Point m n) → ℕ := fun S => (Finset.univ.filter (fun u => Minimal (· ∈ S) u)).card
  have fiber (p : (Point m n) → (Point m n) → Prop) :
      (Finset.univ.filter (fun z : (Point m n) × (Point m n) => p z.1 z.2)).card =
      ∑ a : (Point m n), (Finset.univ.filter (fun b => p b a)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have corner_sum (S : Set (Point m n)) (hS : S.OrdConnected) : H S + A S = E S := by
    rw [show H S = ∑ a : (Point m n), (Finset.univ.filter (fun b =>
        Maximal (· ∈ (lowerClosure S : Set (Point m n)) \ S) b ∧ Maximal (· ∈ S) a ∧
          b.1 < a.1 ∧ b.2 < a.2)).card from by
        convert (fiber (fun b a => Maximal (· ∈ (lowerClosure S : Set (Point m n)) \ S) b ∧
          Maximal (· ∈ S) a ∧ b.1 < a.1 ∧ b.2 < a.2)) using 1
        · apply congrArg Finset.card
          ext z
          simp only [Finset.mem_filter]
        · apply Finset.sum_congr rfl
          intro a _
          apply congrArg Finset.card
          ext b
          simp only [Finset.mem_filter]]
    rw [show E S = ∑ a : (Point m n), (Finset.univ.filter (fun b =>
        Minimal (· ∈ S) b ∧ Maximal (· ∈ S) a ∧ b ≤ a)).card from by
        convert (fiber (fun b a => Minimal (· ∈ S) b ∧ Maximal (· ∈ S) a ∧ b ≤ a)) using 1
        · apply congrArg Finset.card
          ext z
          simp only [Finset.mem_filter]
        · apply Finset.sum_congr rfl
          intro a _
          apply congrArg Finset.card
          ext b
          simp only [Finset.mem_filter]]
    have aa : A S = ∑ a : (Point m n), if Maximal (· ∈ S) a then 1 else 0 := by
      simp only [A, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [aa, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : Maximal (· ∈ S) a
    · have hh := rectangular_corner_card m n S hS a ha.1
      have hc : (Finset.univ.filter (Corner S a)).card =
          (Finset.univ.filter (fun b =>
            Maximal (· ∈ (lowerClosure S : Set (Point m n)) \ S) b ∧
              Maximal (· ∈ S) a ∧ b.1 < a.1 ∧ b.2 < a.2)).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro b _
        simp only [Corner, ha, true_and]
      have hl : (Finset.univ.filter (LocalMin S a)).card =
          (Finset.univ.filter (fun b => Minimal (· ∈ S) b ∧ Maximal (· ∈ S) a ∧ b ≤ a)).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro b _
        simp only [LocalMin, ha, true_and]
      rw [hc, hl] at hh
      simpa only [if_pos ha] using hh
    · simp [ha]
  let r : (Point m n) → (Point m n) := fun x => (x.1.rev, x.2.rev)
  have rr (x : (Point m n)) : r (r x) = x := by simp [r]
  have rle (x y : (Point m n)) : r x ≤ r y ↔ y ≤ x := by
    change x.1.rev ≤ y.1.rev ∧ x.2.rev ≤ y.2.rev ↔ y.1 ≤ x.1 ∧ y.2 ≤ x.2
    simp only [Fin.rev_le_rev]
  have rlt1 (x y : (Point m n)) : (r x).1 < (r y).1 ↔ y.1 < x.1 := Fin.rev_lt_rev
  have rlt2 (x y : (Point m n)) : (r x).2 < (r y).2 ↔ y.2 < x.2 := Fin.rev_lt_rev
  have extrema (p : (Point m n) → Prop) (x : (Point m n)) :
      Minimal (fun y => p (r y)) (r x) ↔ Maximal p x := by
    constructor
    · intro h
      refine ⟨by simpa only [rr] using h.1, ?_⟩
      intro y hy hxy
      have h' := h.2 (by simpa only [rr] using hy : p (r (r y))) ((rle _ _).mpr hxy)
      exact (rle _ _).mp h'
    · intro h
      refine ⟨by simpa only [rr] using h.1, ?_⟩
      intro y hy hyx
      have h' := h.2 hy ((rle (r y) x).mp (by simpa only [rr] using hyx))
      simpa only [rr] using (rle x (r y)).mpr h'
  have dualcorner (S : Set (Point m n)) (hS : S.OrdConnected) : Q S + M S = E S := by
    let T : Set (Point m n) := r ⁻¹' S
    have hT : T.OrdConnected := by
      constructor
      intro x hx y hy z hz
      exact hS.out hy hx ⟨(rle y z).mpr hz.2, (rle z x).mpr hz.1⟩
    have floor (x : (Point m n)) : r x ∈ (lowerClosure T : Set (Point m n)) \ T ↔
        x ∈ (upperClosure S : Set (Point m n)) \ S := by
      constructor
      · rintro ⟨⟨y, hy, hxy⟩, hx⟩
        refine ⟨⟨r y, hy, ?_⟩, ?_⟩
        · have hh := (rle x (r y)).mp (by simpa only [rr] using hxy)
          simpa only [rr] using hh
        · simpa only [T, Set.mem_preimage, rr] using hx
      · rintro ⟨⟨y, hy, hyx⟩, hx⟩
        refine ⟨⟨r y, ?_, (rle x y).mpr hyx⟩, ?_⟩
        · simpa only [T, Set.mem_preimage, rr] using hy
        · simpa only [T, Set.mem_preimage, rr] using hx
    have minmax (x : (Point m n)) : Maximal (· ∈ T) (r x) ↔ Minimal (· ∈ S) x := by
      have h := extrema (fun y => y ∈ T) (r x)
      simpa only [T, Set.mem_preimage, rr] using h.symm
    have maxmin (x : (Point m n)) : Minimal (· ∈ T) (r x) ↔ Maximal (· ∈ S) x := by
      exact extrema (· ∈ S) x
    have ceilfloor (x : (Point m n)) : Maximal (· ∈ (lowerClosure T : Set (Point m n)) \ T) (r x) ↔
        Minimal (· ∈ (upperClosure S : Set (Point m n)) \ S) x := by
      have h := extrema (fun y => y ∈ (lowerClosure T : Set (Point m n)) \ T) (r x)
      simpa only [rr, floor] using h.symm
    have hM : A T = M S := by
      apply Finset.card_bij (fun x _ => r x)
      · intro x hx
        have hh : Maximal (· ∈ T) x := (Finset.mem_filter.mp hx).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (minmax (r x)).mp (by simpa only [rr] using hh)
      · intro x hx y hy hxy
        simpa only [rr] using congrArg r hxy
      · intro y hy
        refine ⟨r y, ?_, rr y⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact (minmax y).mpr hy
    have hH : H T = Q S := by
      apply Finset.card_bij (fun z _ => (r z.2, r z.1))
      · intro z hz
        obtain ⟨hb, ha, h1, h2⟩ := (Finset.mem_filter.mp hz).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(minmax (r z.2)).mp (by simpa only [rr] using ha),
          (ceilfloor (r z.1)).mp (by simpa only [rr] using hb),
          (rlt1 _ _).mpr h1, (rlt2 _ _).mpr h2⟩
      · intro z hz w hw hzw
        apply Prod.ext
        · simpa only [rr] using congrArg (fun v : (Point m n) × (Point m n) => r v.2) hzw
        · simpa only [rr] using congrArg (fun v : (Point m n) × (Point m n) => r v.1) hzw
      · intro z hz
        obtain ⟨hu, hc, h1, h2⟩ := (Finset.mem_filter.mp hz).2
        refine ⟨(r z.2, r z.1), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(ceilfloor _).mpr hc, (minmax _).mpr hu,
            (rlt1 _ _).mpr h1, (rlt2 _ _).mpr h2⟩
        · simp only [rr]
    have hE : E T = E S := by
      apply Finset.card_bij (fun z _ => (r z.2, r z.1))
      · intro z hz
        obtain ⟨hu, ha, hua⟩ := (Finset.mem_filter.mp hz).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(minmax (r z.2)).mp (by simpa only [rr] using ha),
          (maxmin (r z.1)).mp (by simpa only [rr] using hu), (rle _ _).mpr hua⟩
      · intro z hz w hw hzw
        apply Prod.ext
        · simpa only [rr] using congrArg (fun v : (Point m n) × (Point m n) => r v.2) hzw
        · simpa only [rr] using congrArg (fun v : (Point m n) × (Point m n) => r v.1) hzw
      · intro z hz
        obtain ⟨hu, ha, hua⟩ := (Finset.mem_filter.mp hz).2
        refine ⟨(r z.2, r z.1), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(maxmin _).mpr ha, (minmax _).mpr hu, (rle _ _).mpr hua⟩
        · simp only [rr]
    simpa only [hH, hM, hE] using corner_sum T hT
  have convex (S : Set (Point m n)) (hS : S.OrdConnected) : ∀ k, (trace (P := Point m n) e S k).OrdConnected := by
    intro k
    induction k with
    | zero => exact hS
    | succ k ih =>
      by_cases hk : k < N
      · simp only [trace, dif_pos hk]
        unfold toggle
        split
        · assumption
        · exact ih
      · simpa only [trace, dif_neg hk] using ih
  have inv (x : (Point m n)) (S : Set (Point m n)) (hS : S.OrdConnected) : toggle x (toggle x S) = S := by
    unfold toggle
    split
    next h => simp only [symmDiff_symmDiff_cancel_right, if_pos hS]
    next h => simp only
  have dt (x : (Point m n)) (S : Set (Point m n)) : toggle (P := (Point m n)ᵒᵈ) x S = toggle (P := (Point m n)) x S := by
    have h : Set.OrdConnected (α := (Point m n)ᵒᵈ) (S ∆ {x}) ↔ (S ∆ {x}).OrdConnected :=
      Set.ordConnected_dual (α := (Point m n)) (s := S ∆ {x})
    unfold toggle
    exact congrArg (fun q : Prop => if q then S ∆ {x} else S) (propext h)
  let er : Fin N ≃ (Point m n)ᵒᵈ := Fin.revPerm.trans e
  have her : ReverseExtension (P := (Point m n)ᵒᵈ) er := by
    intro x y hxy
    change ((e.symm y).rev).val < ((e.symm x).rev).val
    exact Fin.rev_lt_rev.mpr (he y x hxy)
  have back (S : Set (Point m n)) (hS : S.OrdConnected) : ∀ k, k ≤ N →
      trace (P := (Point m n)ᵒᵈ) er (trace (P := Point m n) e S N) k = trace (P := Point m n) e S (N - k) := by
    intro k
    induction k with
    | zero => intro hk; simp only [trace, Nat.sub_zero]; rfl
    | succ k ih =>
      intro hkN
      have hk : k < N := by omega
      have ht : N - (k + 1) < N := by omega
      have heq : N - k = (N - (k + 1)) + 1 := by omega
      have point : (er ⟨k, hk⟩ : (Point m n)) = e ⟨N - (k + 1), ht⟩ := by
        apply congrArg e
        apply Fin.ext
        rfl
      have stepR : trace (P := (Point m n)ᵒᵈ) er (trace (P := Point m n) e S N) (k + 1) =
          toggle (P := (Point m n)ᵒᵈ) (er ⟨k, hk⟩) (trace (P := (Point m n)ᵒᵈ) er (trace (P := Point m n) e S N) k) := by
        simp only [trace, dif_pos hk]
      have stepF : trace (P := Point m n) e S ((N - (k + 1)) + 1) =
          toggle (P := (Point m n)) (e ⟨N - (k + 1), ht⟩) (trace (P := Point m n) e S (N - (k + 1))) := by
        simp only [trace, dif_pos ht]
      rw [stepR, ih (by omega), heq, point, dt, stepF]
      exact inv _ _ (convex S hS _)
  have recover (S : Set (Point m n)) (hS : S.OrdConnected) :
      trace (P := (Point m n)ᵒᵈ) er (trace (P := Point m n) e S N) N = S := by
    simpa only [Nat.sub_self, trace] using back S hS N le_rfl
  have pair (S : Set (Point m n)) (hS : S.OrdConnected) (b a : (Point m n)) (hba : b < a) :
      (Minimal (· ∈ S) b ∧ Minimal (· ∈ (upperClosure S : Set (Point m n)) \ S) a) ↔
      (Maximal (· ∈ trace (P := Point m n) e S N) a ∧
        Maximal (· ∈ (lowerClosure (trace (P := Point m n) e S N) : Set (Point m n)) \ trace (P := Point m n) e S N) b) := by
    constructor
    · intro h
      exact endpoint_transport e he S hS h.1 h.2 hba
    · rintro ⟨ha, hb⟩
      have hj : Set.OrdConnected (α := (Point m n)ᵒᵈ) (trace (P := Point m n) e S N) :=
        (Set.ordConnected_dual (α := (Point m n))).mpr (convex S hS N)
      have hb' : Minimal (α := (Point m n)ᵒᵈ) (fun x => x ∈
          (upperClosure (α := (Point m n)ᵒᵈ) (trace (P := Point m n) e S N) : Set (Point m n)ᵒᵈ) \ trace (P := Point m n) e S N) b :=
        (minimal_toDual (α := (Point m n))).mpr hb
      have hh := endpoint_transport (P := (Point m n)ᵒᵈ) er her (trace (P := Point m n) e S N) hj
        ((minimal_toDual (α := (Point m n))).mpr ha) hb' hba
      dsimp only at hh
      rw [recover S hS] at hh
      exact hh
  have transport (S : Set (Point m n)) (hS : S.OrdConnected) : H (trace (P := Point m n) e S N) = Q S := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨hb, ha, h1, h2⟩
      have hlt : z.1 < z.2 := lt_of_le_not_ge ⟨le_of_lt h1, le_of_lt h2⟩
        (fun h => (not_le_of_gt h1) h.1)
      exact ⟨((pair S hS _ _ hlt).mpr ⟨ha, hb⟩).1,
        ((pair S hS _ _ hlt).mpr ⟨ha, hb⟩).2, h1, h2⟩
    · rintro ⟨hu, hc, h1, h2⟩
      have hlt : z.1 < z.2 := lt_of_le_not_ge ⟨le_of_lt h1, le_of_lt h2⟩
        (fun h => (not_le_of_gt h1) h.1)
      exact ⟨((pair S hS _ _ hlt).mp ⟨hu, hc⟩).2,
        ((pair S hS _ _ hlt).mp ⟨hu, hc⟩).1, h1, h2⟩
  have coboundary (S : Set (Point m n)) (hS : S.OrdConnected) :
      maxMinusMin S = (H (trace (P := Point m n) e S N) : ℤ) - (H S : ℤ) := by
    have hc := corner_sum S hS
    have hd := dualcorner S hS
    have ht := transport S hS
    have hnat : H (trace (P := Point m n) e S N) + M S = H S + A S := by omega
    have hint : (H (trace (P := Point m n) e S N) : ℤ) + (M S : ℤ) = (H S : ℤ) + (A S : ℤ) := by
      exact_mod_cast hnat
    change (A S : ℤ) - (M S : ℤ) = _
    omega
  let R : Set (Point m n) → Set (Point m n) := fun S => trace (P := Point m n) e S N
  let O : Finset (Set (Point m n)) := literalOrbit e I
  have memO (S : Set (Point m n)) : S ∈ O ↔ ∃ k : ℕ, R^[k] I = S := by simp [O, literalOrbit, R]
  have orbitconvex (S : Set (Point m n)) (hS : S ∈ O) : S.OrdConnected := by
    obtain ⟨k, rfl⟩ := (memO S).mp hS
    clear hS
    induction k with
    | zero => exact hI
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact convex _ ih N
  have closed (S : Set (Point m n)) (hS : S ∈ O) : R S ∈ O := by
    obtain ⟨k, hk⟩ := (memO S).mp hS
    exact (memO (R S)).mpr ⟨k+1, by rw [Function.iterate_succ_apply', hk]⟩
  have injective : Set.InjOn R (O : Set (Set (Point m n))) := by
    intro S hS T hT hST
    have hs := recover S (orbitconvex S hS)
    have ht := recover T (orbitconvex T hT)
    change trace (P := Point m n) e S N = trace (P := Point m n) e T N at hST
    rw [hST] at hs
    exact hs.symm.trans ht
  have imageO : O.image R = O := by
    apply Finset.eq_of_subset_of_card_le
    · intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      exact closed S hS
    · exact (Finset.card_image_of_injOn injective).ge
  have reindex : ∑ S ∈ O, (H (R S) : ℤ) = ∑ S ∈ O, (H S : ℤ) := by
    calc
      _ = ∑ T ∈ O.image R, (H T : ℤ) :=
        (Finset.sum_image (f := fun T => (H T : ℤ))
          (fun S hS T hT hST => injective hS hT hST)).symm
      _ = _ := by rw [imageO]
  change ∑ S ∈ O, maxMinusMin S = 0
  calc
    ∑ S ∈ O, maxMinusMin S = ∑ S ∈ O, ((H (R S) : ℤ) - (H S : ℤ)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact coboundary S (orbitconvex S hS)
    _ = (∑ S ∈ O, (H (R S) : ℤ)) - ∑ S ∈ O, (H S : ℤ) := Finset.sum_sub_distrib _ _
    _ = 0 := by rw [reindex, sub_self]

end D5.S3.Combinatorics.Geometry.RectangleRowmotionHomomesy
