/- GID: D5/S3/Combinatorics/Graph/ActualRectangularResidualBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ActualRectangularResidualBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Actual even rectangular matching residuals and their capacity-port realization. -/

import D5.S3.Combinatorics.Graph.ActualRectangularSaturatedGeometry
import D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
import D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ActualRectangularResidualBridge

open D5.S3.Combinatorics.Graph.CapacityPortParityAbsorption
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.Combinatorics.Graph.ActualRectangularSaturatedGeometry
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 3000000 in
open Classical in
/-- The full actual residual bridge for a feasible matching and singleton set.
All capacities, attachments, coarse edges and routings are derived from the
same original realization. The final inequality is signed integer arithmetic. -/
theorem actual_even_rectangular_residual_bridge
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (E : Type*) [Fintype E] [DecidableEq E]
    (src dst : E → Fin (2 * a) × Fin (2 * b))
    (T : Finset (Fin (2 * a) × Fin (2 * b)))
    (hadj : ∀ e, squareGrid.Adj
      ((src e).1.val, (src e).2.val) ((dst e).1.val, (dst e).2.val))
    (hinj : Function.Injective (fun z : E × Bool => endpoint src dst z.1 z.2))
    (hdisjoint : ∀ e, src e ∉ T ∧ dst e ∉ T)
    (hfeas : ∀ x ∈ T,
      (((T ∪ Finset.univ.image src) ∪ Finset.univ.image dst).filter
        (fun y => squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val))).card ≤ 1) :
    let κ : Fin (2 * a) × Fin (2 * b) → Fin a × Fin b := fun x =>
      (⟨x.1.val / 2, by have := x.1.isLt; omega⟩,
       ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)
    let t : Fin a × Fin b → ℕ := fun Q => (T.filter (fun x => κ x = Q)).card
    let h : Fin a × Fin b → ℕ := fun Q =>
      (Finset.univ.filter (fun e : E => κ (src e) = Q ∧ κ (dst e) = Q)).card
    let s : Fin a × Fin b → ℕ := fun Q =>
      (Finset.univ.filter (fun e : E =>
        (κ (src e) = Q ∧ κ (dst e) ≠ Q ∧ t (κ (dst e)) = 2) ∨
        (κ (dst e) = Q ∧ κ (src e) ≠ Q ∧ t (κ (src e)) = 2))).card
    let r : Fin a × Fin b → ℕ := fun Q => 2 - (t Q + h Q + s Q)
    let ER := {e : E // κ (src e) ≠ κ (dst e) ∧
      t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2}
    let rs : ER → Fin a × Fin b := fun e => κ (src e.val)
    let rd : ER → Fin a × Fin b := fun e => κ (dst e.val)
    let χ : Fin a × Fin b → Bool := fun Q => decide (Odd (Q.1.val + Q.2.val))
    let H := 2 * a * b
    let C := Fintype.card ER
    let R := ∑ Q, r Q
    let K := ∑ Q, (h Q + s Q)
    let ell := (leafVertices rs rd r).card
    let q : ℤ := (T.card : ℤ) + (Fintype.card E : ℤ) - (H : ℤ)
    let D : ℤ := (H : ℤ) - (T.card : ℤ)
    (∀ Q, t Q ≤ 2 ∧ t Q + h Q + s Q + r Q = 2 ∧ r Q ≤ 2) ∧
    (∀ Q, t Q = 2 → h Q = 0 ∧ s Q = 0 ∧ degree rs rd Q = 0) ∧
    (∀ e : E, κ (src e) ≠ κ (dst e) →
      ¬ (t (κ (src e)) = 2 ∧ t (κ (dst e)) = 2)) ∧
    (∀ e : ER, rs e ≠ rd e ∧
      squareGrid.Adj ((rs e).1.val, (rs e).2.val) ((rd e).1.val, (rd e).2.val) ∧
      χ (rs e) ≠ χ (rd e)) ∧
    (∀ Q, r Q = 0 ∧ degree rs rd Q = 1 → 1 ≤ s Q) ∧
    (∀ e : ER, ¬ (r (rs e) = 0 ∧ r (rd e) = 0)) ∧
    ell ≤ ∑ Q, s Q ∧ (∑ Q, s Q) ≤ K ∧
    Fintype.card E = (∑ Q, h Q) + (∑ Q, s Q) + C ∧
    T.card + R + K = H ∧ q = (C : ℤ) - (R : ℤ) ∧ D = (R : ℤ) + (K : ℤ) ∧
    ∃ (hzero : ∀ Q, r Q = 0 → degree rs rd Q ≤ 1)
      (hpos : ∀ Q, 0 < r Q → degree rs rd Q ≤ 2 * r Q)
      (hleaf : ∀ e, ¬ (Leaf rs rd r (rs e) ∧ Leaf rs rd r (rd e)))
      (hK : (leafVertices rs rd r).card ≤ K),
      (∃ σ : Port rs rd r → Port rs rd r,
        (∀ p, σ (σ p) = p) ∧
        (∀ p, portBase rs rd r (σ p) = portBase rs rd r p) ∧
        (∀ p, σ p = p ↔ lPort rs rd r p)) ∧
      ∀ (σ : Port rs rd r → Port rs rd r)
        (hσ : ∀ p, σ (σ p) = p)
        (hbase : ∀ p, portBase rs rd r (σ p) = portBase rs rd r p)
        (hfix : ∀ p, σ p = p ↔ lPort rs rd r p),
        capacityPortClaim rs rd r K σ hσ hbase hfix hzero hpos hleaf hK ∧
        (8 * (a : ℤ) * (b : ℤ) - 4 * (T.card : ℤ) - 3 * (Fintype.card E : ℤ) ≥
          4 * (bCount rs rd r σ hσ : ℤ) + 2 * (cCount rs rd r σ hσ : ℤ) +
          (oddLLCount rs rd r σ hσ : ℤ)) := by
  classical
  intro κ t h s r ER rs rd χ H C R K ell q D
  let A := (T ∪ Finset.univ.image src) ∪ Finset.univ.image dst
  let corner : (Fin a × Fin b) → (Fin 2 × Fin 2) →
      Fin (2 * a) × Fin (2 * b) := fun Q ij =>
    (⟨2 * Q.1.val + ij.1.val, by have := Q.1.isLt; have := ij.1.isLt; omega⟩,
     ⟨2 * Q.2.val + ij.2.val, by have := Q.2.isLt; have := ij.2.isLt; omega⟩)
  let flip : Fin 2 → Fin 2 := fun i => ⟨1 - i.val, by have := i.isLt; omega⟩
  obtain ⟨hTA, hPA, htwo, hcorner, hcornerinj, hfibre, hcorneradj,
    hresidual, ht, hTsum, hbad, hflipne, hnbits, hblank,
    hsatsep, hnosats, hhzero, hszero, hdsat, hattachment⟩ :
    (T ⊆ A) ∧
    (∀ e, src e ∈ A ∧ dst e ∈ A) ∧
    (∀ x ∈ T, ∀ y z, y ∈ A → z ∈ A →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      squareGrid.Adj (x.1.val, x.2.val) (z.1.val, z.2.val) → y = z) ∧
    (∀ Q ij, κ (corner Q ij) = Q) ∧
    (∀ Q, Function.Injective (corner Q)) ∧
    (∀ Q x, κ x = Q ↔ ∃ ij, corner Q ij = x) ∧
    (∀ Q ij kl,
      squareGrid.Adj ((corner Q ij).1.val, (corner Q ij).2.val)
        ((corner Q kl).1.val, (corner Q kl).2.val) ↔
      (ij.1 = kl.1 ∧ ij.2 ≠ kl.2) ∨ (ij.2 = kl.2 ∧ ij.1 ≠ kl.1)) ∧
    (∀ e : ER, rs e ≠ rd e ∧
      squareGrid.Adj ((rs e).1.val, (rs e).2.val) ((rd e).1.val, (rd e).2.val) ∧
      χ (rs e) ≠ χ (rd e)) ∧
    (∀ Q, t Q ≤ 2) ∧
    (∀ Q, t Q =
      (if corner Q (0,0) ∈ T then 1 else 0) +
      (if corner Q (0,1) ∈ T then 1 else 0) +
      (if corner Q (1,0) ∈ T then 1 else 0) +
      (if corner Q (1,1) ∈ T then 1 else 0)) ∧
    (∀ Q (i j k : Fin 2 × Fin 2), j ≠ k →
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      ((i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1)) →
      corner Q i ∈ T → corner Q j ∈ A → corner Q k ∈ A → False) ∧
    (∀ i, flip i ≠ i) ∧
    (∀ i j : Fin 2 × Fin 2,
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      j = (flip i.1,i.2) ∨ j = (i.1,flip i.2)) ∧
    (∀ Q Q' (i j : Fin 2 × Fin 2), Q ≠ Q' →
      squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val)
        ((corner Q' j).1.val, (corner Q' j).2.val) →
      t Q = 2 → corner Q i ∈ A → corner Q i ∉ T →
      ∃ z w : Fin (2 * a) × Fin (2 * b),
        z ∈ T ∧ κ z = Q ∧ κ w = Q' ∧
        squareGrid.Adj ((corner Q i).1.val, (corner Q i).2.val) (z.1.val, z.2.val) ∧
        squareGrid.Adj ((corner Q' j).1.val, (corner Q' j).2.val) (w.1.val, w.2.val) ∧
        squareGrid.Adj (z.1.val, z.2.val) (w.1.val, w.2.val) ∧ w ∉ A) ∧
    (∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x ≠ κ y → squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      t (κ x) = 2 → t (κ y) = 2 →
      x ∈ A → x ∉ T → y ∈ A → y ∉ T → False) ∧
    (∀ e : E, κ (src e) ≠ κ (dst e) →
      ¬ (t (κ (src e)) = 2 ∧ t (κ (dst e)) = 2)) ∧
    (∀ Q, t Q = 2 → h Q = 0) ∧
    (∀ Q, t Q = 2 → s Q = 0) ∧
    (∀ Q, t Q = 2 → degree rs rd Q = 0) ∧
    (∀ x y : Fin (2 * a) × Fin (2 * b),
      κ x ≠ κ y →
      squareGrid.Adj (x.1.val, x.2.val) (y.1.val, y.2.val) →
      t (κ x) = 2 → x ∈ A → x ∉ T →
      ∃ w : Fin (2 * a) × Fin (2 * b), κ w = κ y ∧
        squareGrid.Adj (y.1.val, y.2.val) (w.1.val, w.2.val) ∧ w ∉ A) :=
    actual_even_rectangular_saturated_geometry a b ha hb E src dst T
      hadj hinj hdisjoint hfeas
  let attach : (Fin a × Fin b) → E → Prop := fun Q e =>
    (κ (src e) = Q ∧ κ (dst e) ≠ Q ∧ t (κ (dst e)) = 2) ∨
    (κ (dst e) = Q ∧ κ (src e) ≠ Q ∧ t (κ (src e)) = 2)
  let receive : (Fin a × Fin b) → E → Fin (2 * a) × Fin (2 * b) :=
    fun Q e => if κ (src e) = Q then src e else dst e
  have hreceiveinj : ∀ Q, Function.Injective (receive Q) := by
    intro Q e f he
    let be := decide (κ (src e) ≠ Q)
    let bf := decide (κ (src f) ≠ Q)
    have heq : endpoint src dst e be = endpoint src dst f bf := by
      simpa [endpoint,be,bf,receive] using he
    exact congrArg Prod.fst (@hinj (e,be) (f,bf) heq)
  have hreceive : ∀ Q e, attach Q e → κ (receive Q e) = Q ∧
      receive Q e ∈ A ∧ receive Q e ∉ T ∧
      ∃ w : Fin (2 * a) × Fin (2 * b), κ w = Q ∧
        squareGrid.Adj ((receive Q e).1.val, (receive Q e).2.val)
          (w.1.val, w.2.val) ∧ w ∉ A := by
    intro Q e he
    rcases he with ⟨hs,hd,htd⟩ | ⟨hd,hs,hts⟩
    · have hn : κ (dst e) ≠ κ (src e) := by rw [hs]; exact hd
      obtain ⟨w,hwQ,had,hwA⟩ := hattachment (dst e) (src e) hn
        (hadj e).symm htd (hPA e).2 (hdisjoint e).2
      simp only [receive,if_pos hs]
      exact ⟨hs,(hPA e).1,(hdisjoint e).1,w,hwQ.trans hs,had,hwA⟩
    · have hn : κ (src e) ≠ κ (dst e) := by rw [hd]; exact hs
      obtain ⟨w,hwQ,had,hwA⟩ := hattachment (src e) (dst e) hn
        (hadj e) hts (hPA e).1 (hdisjoint e).1
      simp only [receive,if_neg hs]
      exact ⟨hd,(hPA e).2,(hdisjoint e).2,w,hwQ.trans hd,had,hwA⟩
  let pCorners : (Fin a × Fin b) → Finset (Fin 2 × Fin 2) := fun Q =>
    Finset.univ.filter (fun i => ∃ z : E × Bool, endpoint src dst z.1 z.2 = corner Q i)
  let sCorners : (Fin a × Fin b) → Finset (Fin 2 × Fin 2) := fun Q =>
    Finset.univ.filter (fun i => ∃ e : E, attach Q e ∧ receive Q e = corner Q i)
  have hpCorner : ∀ Q i, i ∈ pCorners Q → corner Q i ∈ A ∧ corner Q i ∉ T := by
    intro Q i hi
    obtain ⟨⟨e,bb⟩,he⟩ := (Finset.mem_filter.mp hi).2
    cases bb
    · change src e = corner Q i at he
      rw [← he]
      exact ⟨(hPA e).1,(hdisjoint e).1⟩
    · change dst e = corner Q i at he
      rw [← he]
      exact ⟨(hPA e).2,(hdisjoint e).2⟩
  have hsCorner : ∀ Q i, i ∈ sCorners Q → i ∈ pCorners Q ∧
      ∃ j : Fin 2 × Fin 2,
        ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) ∧
        corner Q j ∉ A := by
    intro Q i hi
    obtain ⟨e,he,hei⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hq,hA,hT,w,hw,had,hwA⟩ := hreceive Q e he
    obtain ⟨j,hj⟩ := (hfibre Q w).mp hw
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,j,?_,?_⟩
    · by_cases hx : κ (src e) = Q
      · exact ⟨(e,false),by simpa only [receive,if_pos hx,endpoint,Bool.false_eq_true,if_false] using hei⟩
      · exact ⟨(e,true),by simpa only [receive,if_neg hx,endpoint,if_true] using hei⟩
    · exact (hcorneradj Q i j).mp (by simpa only [hei,hj] using had)
    · simpa only [hj] using hwA
  have hfourCount : ∀ U : Finset (Fin 2 × Fin 2), U.card =
      (if (0,0) ∈ U then 1 else 0) + (if (0,1) ∈ U then 1 else 0) +
      (if (1,0) ∈ U then 1 else 0) + (if (1,1) ∈ U then 1 else 0) := by
    intro U
    have hu : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0,0), (0,1), (1,0), (1,1)} := by decide
    calc
      U.card = (Finset.univ.filter (fun i => i ∈ U)).card := by simp
      _ = ∑ i : Fin 2 × Fin 2, if i ∈ U then 1 else 0 := Finset.card_filter _ _
      _ = _ := by
        rw [hu,Finset.sum_insert (by decide),Finset.sum_insert (by decide),
          Finset.sum_insert (by decide),Finset.sum_singleton]
        omega
  have hsCount : ∀ Q, (sCorners Q).card = s Q := by
    intro Q
    have hi : (sCorners Q).image (corner Q) =
        (Finset.univ.filter (attach Q)).image (receive Q) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨e,he,hei⟩ := (Finset.mem_filter.mp hi).2
        exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hei⟩
      · intro hx
        obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
        have he' := (Finset.mem_filter.mp he).2
        obtain ⟨i,hi⟩ := (hfibre Q (receive Q e)).mp (hreceive Q e he').1
        exact Finset.mem_image.mpr ⟨i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he',hi.symm⟩,hi⟩
    have hc := congrArg Finset.card hi
    rw [Finset.card_image_of_injective _ (hcornerinj Q),
      Finset.card_image_of_injective _ (hreceiveinj Q)] at hc
    exact hc
  have hpCount : ∀ Q, (pCorners Q).card =
      (Finset.univ.filter (fun z : E × Bool => κ (endpoint src dst z.1 z.2) = Q)).card := by
    intro Q
    have hi : (pCorners Q).image (corner Q) =
        (Finset.univ.filter (fun z : E × Bool => κ (endpoint src dst z.1 z.2) = Q)).image
          (fun z => endpoint src dst z.1 z.2) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hi).2
        exact Finset.mem_image.mpr ⟨z,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hz]; exact hcorner Q i⟩,hz⟩
      · intro hx
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨i,hi⟩ := (hfibre Q (endpoint src dst z.1 z.2)).mp (Finset.mem_filter.mp hz).2
        exact Finset.mem_image.mpr ⟨i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hi.symm⟩,hi⟩
    have hc := congrArg Finset.card hi
    rw [Finset.card_image_of_injective _ (hcornerinj Q),
      Finset.card_image_of_injective _ hinj] at hc
    exact hc
  let tCorners : (Fin a × Fin b) → Finset (Fin 2 × Fin 2) := fun Q =>
    Finset.univ.filter (fun i => corner Q i ∈ T)
  have htCount : ∀ Q, (tCorners Q).card = t Q := by
    intro Q
    rw [hfourCount]
    simpa only [tCorners,Finset.mem_filter,Finset.mem_univ,true_and] using (hTsum Q).symm
  have htpDisjoint : ∀ Q, Disjoint (tCorners Q) (pCorners Q) := by
    intro Q
    apply Finset.disjoint_left.mpr
    intro i hi hp
    exact (hpCorner Q i hp).2 (Finset.mem_filter.mp hi).2
  have hNeighborCover : ∀ i j k l : Fin 2 × Fin 2, j ≠ k →
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      ((i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1)) →
      ((i.1 = l.1 ∧ i.2 ≠ l.2) ∨ (i.2 = l.2 ∧ i.1 ≠ l.1)) → l = j ∨ l = k := by
    intro i j k l hjk hij hik hil
    rcases hnbits i j hij with rfl | rfl <;>
      rcases hnbits i k hik with rfl | rfl <;>
      rcases hnbits i l hil with rfl | rfl
    all_goals first | exact False.elim (hjk rfl) | exact Or.inl rfl | exact Or.inr rfl
  have hSmall : ∀ U : Finset (Fin 2 × Fin 2),
      (∀ i j k : Fin 2 × Fin 2, i ∈ U → j ∈ U → k ∈ U → j ≠ k →
        ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
        ((i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1)) → False) →
      U.card ≤ 2 := by
    intro U htrip
    have hn0 : ¬ ((0,0) ∈ U ∧ (0,1) ∈ U ∧ (1,0) ∈ U) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (0,0) (0,1) (1,0) h0 h1 h2 (by decide) (by decide) (by decide)
    have hn1 : ¬ ((0,0) ∈ U ∧ (0,1) ∈ U ∧ (1,1) ∈ U) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (0,1) (0,0) (1,1) h1 h0 h2 (by decide) (by decide) (by decide)
    have hn2 : ¬ ((0,0) ∈ U ∧ (1,0) ∈ U ∧ (1,1) ∈ U) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (1,0) (0,0) (1,1) h1 h0 h2 (by decide) (by decide) (by decide)
    have hn3 : ¬ ((0,1) ∈ U ∧ (1,0) ∈ U ∧ (1,1) ∈ U) := by
      rintro ⟨h0,h1,h2⟩
      exact htrip (1,1) (0,1) (1,0) h2 h0 h1 (by decide) (by decide) (by decide)
    rw [hfourCount]
    split_ifs <;> first
    | omega
    | exact False.elim (hn0 ⟨by assumption,by assumption,by assumption⟩)
    | exact False.elim (hn1 ⟨by assumption,by assumption,by assumption⟩)
    | exact False.elim (hn2 ⟨by assumption,by assumption,by assumption⟩)
    | exact False.elim (hn3 ⟨by assumption,by assumption,by assumption⟩)
  have hTSbudget : ∀ Q, t Q + s Q ≤ 2 := by
    intro Q
    let U := tCorners Q ∪ sCorners Q
    have hUA : ∀ i, i ∈ U → corner Q i ∈ A := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hTA (Finset.mem_filter.mp hi).2
      · exact (hpCorner Q i (hsCorner Q i hi).1).1
    have hUcard : U.card ≤ 2 := by
      apply hSmall U
      intro i j k hi hj hk hjk hij hik
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hbad Q i j k hjk hij hik (Finset.mem_filter.mp hi).2
          (hUA j hj) (hUA k hk)
      · obtain ⟨hp,l,hil,hlA⟩ := hsCorner Q i hi
        rcases hNeighborCover i j k l hjk hij hik hil with rfl | rfl
        · exact hlA (hUA _ hj)
        · exact hlA (hUA _ hk)
    have hdisj : Disjoint (tCorners Q) (sCorners Q) := by
      apply Finset.disjoint_left.mpr
      intro i hi hs
      exact (hpCorner Q i (hsCorner Q i hs).1).2 (Finset.mem_filter.mp hi).2
    rw [Finset.card_union_of_disjoint hdisj,htCount,hsCount] at hUcard
    exact hUcard
  have hPmax : ∀ Q, t Q + (pCorners Q).card ≤ 4 := by
    intro Q
    have hc := Finset.card_le_card (Finset.subset_univ (tCorners Q ∪ pCorners Q))
    rw [Finset.card_union_of_disjoint (htpDisjoint Q),htCount] at hc
    simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using hc
  have hPblank : ∀ Q, 0 < s Q → t Q + (pCorners Q).card ≤ 3 := by
    intro Q hs
    have hc : 0 < (sCorners Q).card := by rw [hsCount]; exact hs
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hc
    obtain ⟨hp,j,hij,hjA⟩ := hsCorner Q i hi
    have hj : j ∉ tCorners Q ∪ pCorners Q := by
      intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hjA (hTA (Finset.mem_filter.mp hj).2)
      · exact hjA (hpCorner Q j hj).1
    have hstrict : tCorners Q ∪ pCorners Q ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _,?_⟩
      intro he
      exact hj (he.symm ▸ Finset.mem_univ j)
    have hlt := Finset.card_lt_card hstrict
    rw [Finset.card_union_of_disjoint (htpDisjoint Q),htCount] at hlt
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at hlt
    omega
  have hOpposite : ∀ i j : Fin 2 × Fin 2, i ≠ j →
      ¬ ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1)) →
      j = (flip i.1,flip i.2) := by
    intro i j hij hnot
    have h0 : i.1 ≠ j.1 := by
      intro he
      have hn : i.2 ≠ j.2 := fun hh => hij (Prod.ext he hh)
      exact hnot (Or.inl ⟨he,hn⟩)
    have h1 : i.2 ≠ j.2 := by
      intro he
      exact hnot (Or.inr ⟨he,h0⟩)
    have hi0 := i.1.isLt
    have hi1 := i.2.isLt
    have hj0 := j.1.isLt
    have hj1 := j.2.isLt
    have hn0 : i.1.val ≠ j.1.val := fun he => h0 (Fin.ext he)
    have hn1 : i.2.val ≠ j.2.val := fun he => h1 (Fin.ext he)
    apply Prod.ext <;> apply Fin.ext <;> dsimp [flip] <;> omega
  have hPtwo : ∀ Q, 0 < t Q → (pCorners Q).card ≤ 2 := by
    intro Q htpos
    have hc : 0 < (tCorners Q).card := by rw [htCount]; exact htpos
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hc
    have hiT := (Finset.mem_filter.mp hi).2
    let adj : (Fin 2 × Fin 2) → Prop := fun j =>
      ((i.1 = j.1 ∧ i.2 ≠ j.2) ∨ (i.2 = j.2 ∧ i.1 ≠ j.1))
    have hn : ((pCorners Q).filter adj).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      have hj' := Finset.mem_filter.mp hj
      have hk' := Finset.mem_filter.mp hk
      exact hcornerinj Q (htwo (corner Q i) hiT (corner Q j) (corner Q k)
        (hpCorner Q j hj'.1).1 (hpCorner Q k hk'.1).1
        ((hcorneradj Q i j).mpr hj'.2) ((hcorneradj Q i k).mpr hk'.2))
    have ho : ((pCorners Q).filter (fun j => ¬ adj j)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      have hj' := Finset.mem_filter.mp hj
      have hk' := Finset.mem_filter.mp hk
      have hij : i ≠ j := by
        intro he
        exact (hpCorner Q j hj'.1).2 (he ▸ hiT)
      have hik : i ≠ k := by
        intro he
        exact (hpCorner Q k hk'.1).2 (he ▸ hiT)
      exact (hOpposite i j hij hj'.2).trans (hOpposite i k hik hk'.2).symm
    have hpart := Finset.card_filter_add_card_filter_not (s := pCorners Q) adj
    omega
  have hDegreeSum : ∀ Q, degree rs rd Q = ∑ e : E,
      if κ (src e) ≠ κ (dst e) ∧ t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2 then
        (if κ (dst e) = Q then 1 else 0) + (if κ (src e) = Q then 1 else 0)
      else 0 := by
    intro Q
    rw [degree,Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,endpoint,if_true,Bool.false_eq_true,if_false]
    change (∑ e : ER, ((if κ (dst e.val) = Q then 1 else 0) +
      (if κ (src e.val) = Q then 1 else 0))) = _
    rw [← Finset.sum_subtype
      (Finset.univ.filter (fun e : E => κ (src e) ≠ κ (dst e) ∧
        t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2))
      (by intro e; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
      (fun e : E => (if κ (dst e) = Q then 1 else 0) + (if κ (src e) = Q then 1 else 0)),
      Finset.sum_filter]
  have hPledger : ∀ Q, t Q < 2 →
      (pCorners Q).card = 2 * h Q + s Q + degree rs rd Q := by
    intro Q hQ
    have hps : (pCorners Q).card = ∑ e : E,
        ((if κ (dst e) = Q then 1 else 0) + (if κ (src e) = Q then 1 else 0)) := by
      rw [hpCount,Finset.card_filter,Fintype.sum_prod_type]
      simp only [Fintype.sum_bool,endpoint,if_true,Bool.false_eq_true,if_false]
    rw [hps,hDegreeSum]
    change _ = 2 * (Finset.univ.filter (fun e : E => κ (src e) = Q ∧ κ (dst e) = Q)).card +
      (Finset.univ.filter (attach Q)).card + _
    rw [Finset.card_filter,Finset.card_filter,Finset.mul_sum,
      ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have hts := ht (κ (src e))
    have htd := ht (κ (dst e))
    by_cases hs : κ (src e) = Q
    · by_cases hd : κ (dst e) = Q
      · simp [attach,hs,hd]
      · by_cases hd2 : t (κ (dst e)) = 2
        · simp [attach,hs,hd,ne_comm,hQ,hd2]
        · have hdlt : t (κ (dst e)) < 2 := by omega
          simp [attach,hs,hd,Ne.symm hd,hQ,hd2,hdlt]
    · by_cases hd : κ (dst e) = Q
      · by_cases hs2 : t (κ (src e)) = 2
        · simp [attach,hs,hd,hQ,hs2]
        · have hslt : t (κ (src e)) < 2 := by omega
          simp [attach,hs,hd,hQ,hs2,hslt]
      · simp [attach,hs,hd]
  have hLocal : ∀ Q,
      (t Q + h Q + s Q ≤ 2) ∧
      (r Q = 0 → degree rs rd Q ≤ 1) ∧
      (0 < r Q → degree rs rd Q ≤ 2 * r Q) ∧
      (r Q = 0 ∧ degree rs rd Q = 1 → 1 ≤ s Q) := by
    intro Q
    have htQ := ht Q
    by_cases ht2 : t Q = 2
    · have hh := hhzero Q ht2
      have hs := hszero Q ht2
      have hd := hdsat Q ht2
      dsimp only [r]
      omega
    · have htlt : t Q < 2 := by omega
      have hp := hPledger Q htlt
      have hmax := hPmax Q
      have hts := hTSbudget Q
      have hs : s Q = 0 ∨ t Q + (pCorners Q).card ≤ 3 := by
        by_cases hz : s Q = 0
        · exact Or.inl hz
        · exact Or.inr (hPblank Q (by omega))
      have htwo : t Q = 0 ∨ (pCorners Q).card ≤ 2 := by
        by_cases hz : t Q = 0
        · exact Or.inl hz
        · exact Or.inr (hPtwo Q (by omega))
      dsimp only [r]
      omega
  have hbudget : ∀ Q, t Q + h Q + s Q ≤ 2 := fun Q => (hLocal Q).1
  have hzero : ∀ Q, r Q = 0 → degree rs rd Q ≤ 1 := fun Q => (hLocal Q).2.1
  have hpos : ∀ Q, 0 < r Q → degree rs rd Q ≤ 2 * r Q := fun Q => (hLocal Q).2.2.1
  have hleafS : ∀ Q, r Q = 0 ∧ degree rs rd Q = 1 → 1 ≤ s Q := fun Q => (hLocal Q).2.2.2
  have hellS : ell ≤ ∑ Q, s Q := by
    change (Finset.univ.filter (Leaf rs rd r)).card ≤ _
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro Q hQ
    by_cases hl : Leaf rs rd r Q
    · simpa only [if_pos hl] using hleafS Q hl
    · simp only [if_neg hl,Nat.zero_le]
  have hZeroData : ∀ Q, r Q = 0 → 0 < degree rs rd Q →
      t Q < 2 ∧ h Q = 0 ∧ t Q + s Q = 2 ∧ degree rs rd Q = 1 ∧
      (pCorners Q).card = s Q + 1 := by
    intro Q hr hdpos
    have htQ := ht Q
    have htlt : t Q < 2 := by
      by_contra hn
      have ht2 : t Q = 2 := by omega
      have hd := hdsat Q ht2
      omega
    have hp := hPledger Q htlt
    have hmax := hPmax Q
    have hdeg := hzero Q hr
    have hspos := hleafS Q ⟨hr,by omega⟩
    have hblank := hPblank Q (by omega)
    have htwo : t Q = 0 ∨ (pCorners Q).card ≤ 2 := by
      by_cases hz : t Q = 0
      · exact Or.inl hz
      · exact Or.inr (hPtwo Q (by omega))
    change 2 - (t Q + h Q + s Q) = 0 at hr
    have hb := hbudget Q
    omega
  have hResidualNotAttach : ∀ (e : ER) (bb : Bool) Q i,
      endpoint src dst e.val bb = corner Q i → i ∉ sCorners Q := by
    intro e bb Q i hei his
    obtain ⟨f,hf,hfi⟩ := (Finset.mem_filter.mp his).2
    let bf := decide (κ (src f) ≠ Q)
    have hfend : endpoint src dst f bf = receive Q f := by
      simp [endpoint,bf,receive]
    have heq : (e.val,bb) = (f,bf) :=
      @hinj (e.val,bb) (f,bf) (hei.trans (hfend.trans hfi).symm)
    have hef : e.val = f := congrArg Prod.fst heq
    have hslt := e.property.2.1
    have hdlt := e.property.2.2
    rcases hf with ⟨hs,hd,htd⟩ | ⟨hd,hs,hts⟩
    · have hh : t (κ (dst e.val)) = 2 := by rw [hef]; exact htd
      omega
    · have hh : t (κ (src e.val)) = 2 := by rw [hef]; exact hts
      omega
  have hEledger : Fintype.card E = (∑ Q, h Q) + (∑ Q, s Q) + C := by
    have hh : (∑ Q, h Q) = ∑ e : E,
        (∑ Q : Fin a × Fin b, if κ (src e) = Q ∧ κ (dst e) = Q then 1 else 0) := by
      dsimp only [h]
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    have hs : (∑ Q, s Q) = ∑ e : E,
        (∑ Q : Fin a × Fin b, if attach Q e then 1 else 0) := by
      change (∑ Q, (Finset.univ.filter (attach Q)).card) = _
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    have hc : C = ∑ e : E,
        if κ (src e) ≠ κ (dst e) ∧ t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2 then 1 else 0 := by
      dsimp only [C,ER]
      rw [Fintype.card_subtype,Finset.card_filter]
    have hpartition : ∀ e : E,
        (∑ Q : Fin a × Fin b, if κ (src e) = Q ∧ κ (dst e) = Q then 1 else 0) +
        (∑ Q : Fin a × Fin b, if attach Q e then 1 else 0) +
        (if κ (src e) ≠ κ (dst e) ∧ t (κ (src e)) < 2 ∧ t (κ (dst e)) < 2 then 1 else 0) = 1 := by
      intro e
      by_cases he : κ (src e) = κ (dst e)
      · simp [attach,he]
      · have hi : ∀ Q, ¬ (κ (src e) = Q ∧ κ (dst e) = Q) := by
          rintro Q ⟨hs,hd⟩
          exact he (hs.trans hd.symm)
        have ha : ∀ Q, attach Q e ↔
            (κ (src e) = Q ∧ t (κ (dst e)) = 2) ∨
            (κ (dst e) = Q ∧ t (κ (src e)) = 2) := by
          intro Q
          constructor
          · rintro (⟨hs,hd,ht⟩ | ⟨hd,hs,ht⟩)
            · exact Or.inl ⟨hs,ht⟩
            · exact Or.inr ⟨hd,ht⟩
          · rintro (⟨hs,ht⟩ | ⟨hd,ht⟩)
            · exact Or.inl ⟨hs,by intro hd; exact he (hs.trans hd.symm),ht⟩
            · exact Or.inr ⟨hd,by intro hs; exact he (hs.trans hd.symm),ht⟩
        have hts := ht (κ (src e))
        have htd := ht (κ (dst e))
        by_cases hs2 : t (κ (src e)) = 2
        · have hd2 : t (κ (dst e)) ≠ 2 := by
            intro hd2
            exact hnosats e he ⟨hs2,hd2⟩
          have hsnot : ¬ t (κ (src e)) < 2 := by omega
          simp only [hi,if_false,Finset.sum_const_zero,ha,hs2,hd2,and_false,and_true,
            false_or,hsnot,false_and,if_false,zero_add,add_zero]
          simp
        · by_cases hd2 : t (κ (dst e)) = 2
          · have hdnot : ¬ t (κ (dst e)) < 2 := by omega
            simp only [hi,if_false,Finset.sum_const_zero,ha,hs2,hd2,and_false,and_true,
              or_false,hdnot,and_false,if_false,zero_add,add_zero]
            simp
          · have hslt : t (κ (src e)) < 2 := by omega
            have hdlt : t (κ (dst e)) < 2 := by omega
            simp [hi,ha,hs2,hd2,he,hslt,hdlt]
    have hp := Finset.sum_congr (s₁ := (Finset.univ : Finset E)) (s₂ := Finset.univ)
      rfl (fun e _ => hpartition e)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← hh,← hs,← hc] at hp
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hp.symm
  have hTledger : T.card = ∑ Q, t Q := by
    exact Finset.card_eq_sum_card_fiberwise (f := κ)
      (s := T) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hpairing :
      (∀ Q, r Q = 0 → degree rs rd Q ≤ 1) →
      (∀ Q, 0 < r Q → degree rs rd Q ≤ 2 * r Q) →
      ∃ σ : Port rs rd r → Port rs rd r,
        (∀ p, σ (σ p) = p) ∧
        (∀ p, portBase rs rd r (σ p) = portBase rs rd r p) ∧
        (∀ p, σ p = p ↔ lPort rs rd r p) := by
    intro hzero hpos
    let P := Port rs rd r
    let base : P → Fin a × Fin b := portBase rs rd r
    let U : (Fin a × Fin b) → Set P := fun Q => {p | base p = Q}
    have hcard : ∀ Q, Fintype.card (U Q) = degree rs rd Q + (2 * r Q - degree rs rd Q) := by
      intro Q
      let eqv : U Q ≃ {z : ER × Bool // endpoint rs rd z.1 z.2 = Q} ⊕
          Fin (2 * r Q - degree rs rd Q) :=
        Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaSubtype Q))
      calc
        Fintype.card (U Q) = Fintype.card
            ({z : ER × Bool // endpoint rs rd z.1 z.2 = Q} ⊕
              Fin (2 * r Q - degree rs rd Q)) := Fintype.card_congr eqv
        _ = Fintype.card {z : ER × Bool // endpoint rs rd z.1 z.2 = Q} +
            Fintype.card (Fin (2 * r Q - degree rs rd Q)) := by
          convert Fintype.card_sum (α := {z : ER × Bool // endpoint rs rd z.1 z.2 = Q})
            (β := Fin (2 * r Q - degree rs rd Q)) using 1
        _ = _ := by rw [Fintype.card_fin]; rfl
    have hex : ∀ Q : {Q : Fin a × Fin b // 0 < r Q},
        ∃ M : (⊤ : SimpleGraph P).Subgraph, M.verts = U Q.val ∧ M.IsMatching := by
      intro Q
      have hc : (⊤ : SimpleGraph P).IsClique (U Q.val) := by
        intro p hp q hq hpq
        exact hpq
      have heven : Even (U Q.val).ncard := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, hcard]
        have hd := hpos Q.val Q.property
        exact ⟨r Q.val, by omega⟩
      exact (hc.even_iff_exists_isMatching (Set.toFinite _)).mp heven
    choose M hMverts hMmatch using hex
    have hmem : ∀ (p : P) (hp : 0 < r (base p)),
        p ∈ (M ⟨base p,hp⟩).verts := by
      intro p hp
      rw [hMverts]
      rfl
    let mate : ∀ (p : P), 0 < r (base p) → P :=
      fun p hp => (hMmatch ⟨base p,hp⟩ (hmem p hp)).choose
    have hmate : ∀ p hp, (M ⟨base p,hp⟩).Adj p (mate p hp) := by
      intro p hp
      exact (hMmatch ⟨base p,hp⟩ (hmem p hp)).choose_spec.1
    let σ : P → P := fun p => if hp : 0 < r (base p) then mate p hp else p
    have hedge : ∀ p hp, (M ⟨base p,hp⟩).Adj p (σ p) := by
      intro p hp
      dsimp only [σ]
      rw [dif_pos hp]
      exact hmate p hp
    have hbase : ∀ p, base (σ p) = base p := by
      intro p
      by_cases hp : 0 < r (base p)
      · have hm := (hedge p hp).snd_mem
        rw [hMverts] at hm
        exact hm
      · simp only [σ, dif_neg hp]
    have hinvol : ∀ p, σ (σ p) = p := by
      intro p
      by_cases hp : 0 < r (base p)
      · have hp' : 0 < r (base (σ p)) := by rw [hbase]; exact hp
        have hi : (⟨base (σ p),hp'⟩ : {Q : Fin a × Fin b // 0 < r Q}) =
            ⟨base p,hp⟩ := Subtype.ext (hbase p)
        have he := hedge (σ p) hp'
        rw [hi] at he
        exact (hMmatch ⟨base p,hp⟩).eq_of_adj_left he (hedge p hp).symm
      · have he : σ p = p := by simp only [σ, dif_neg hp]
        rw [he,he]
    have hfix : ∀ p, σ p = p ↔ lPort rs rd r p := by
      intro p
      constructor
      · intro he
        have hp : ¬ 0 < r (base p) := by
          intro hp
          exact (hedge p hp).ne he.symm
        have hr : r (base p) = 0 := by omega
        cases p with
        | inl z =>
          rcases z with ⟨e,bb⟩
          have hd := hzero (base (Sum.inl (e,bb))) hr
          have hdpos : 0 < degree rs rd (base (Sum.inl (e,bb))) := by
            apply Fintype.card_pos_iff.mpr
            exact ⟨⟨(e,bb),rfl⟩⟩
          have hdscalar : degree rs rd (endpoint rs rd e bb) = 1 := by
            change degree rs rd (endpoint rs rd e bb) ≤ 1 at hd
            change 0 < degree rs rd (endpoint rs rd e bb) at hdpos
            omega
          exact ⟨⟨e,bb,rfl⟩,hr,hdscalar⟩
        | inr z =>
          rcases z with ⟨Q,i⟩
          change r Q = 0 at hr
          have hi : i.val < 2 * r Q - degree rs rd Q := i.isLt
          omega
      · intro hp
        have hr : ¬ 0 < r (base p) := by
          have hz := hp.2.1
          change r (base p) = 0 at hz
          omega
        simp only [σ, dif_neg hr]
    exact ⟨σ,hinvol,hbase,hfix⟩
  suffices remaining :
      (∀ Q, t Q + h Q + s Q ≤ 2) ∧
      (∀ Q, r Q = 0 → degree rs rd Q ≤ 1) ∧
      (∀ Q, 0 < r Q → degree rs rd Q ≤ 2 * r Q) ∧
      (∀ Q, r Q = 0 ∧ degree rs rd Q = 1 → 1 ≤ s Q) ∧
      (∀ e : ER, ¬ (r (rs e) = 0 ∧ r (rd e) = 0)) ∧
      ell ≤ ∑ Q, s Q ∧
      Fintype.card E = (∑ Q, h Q) + (∑ Q, s Q) + C by
    rcases remaining with ⟨hbudget,hzero,hpos,hleafS,hphysical,hellS,hEledger⟩
    have hrouting := hpairing hzero hpos
    have hcap : ∀ Q, t Q + h Q + s Q + r Q = 2 := by
      intro Q
      have hh := hbudget Q
      dsimp [r]
      omega
    have hSleK : (∑ Q, s Q) ≤ K := by
      dsimp [K]
      exact Finset.sum_le_sum (fun Q _ => Nat.le_add_left (s Q) (h Q))
    have hK : (leafVertices rs rd r).card ≤ K := hellS.trans hSleK
    have hleaf : ∀ e, ¬ (Leaf rs rd r (rs e) ∧ Leaf rs rd r (rd e)) := by
      rintro e ⟨hs,hd⟩
      exact hphysical e ⟨hs.1,hd.1⟩
    have hEK : Fintype.card E = K + C := by
      simpa only [K, Finset.sum_add_distrib] using hEledger
    have hcapacityLedger : T.card + R + K = H := by
      have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
        rfl (fun Q _ => hcap Q)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at hs
      rw [← hTledger] at hs
      dsimp only [R,K,H]
      rw [Finset.sum_add_distrib]
      nlinarith [hs]
    have hq : q = (C : ℤ) - (R : ℤ) := by
      dsimp only [q]
      omega
    have hD : D = (R : ℤ) + (K : ℤ) := by
      dsimp only [D]
      omega
    refine ⟨?_,?_,hnosats,hresidual,hleafS,hphysical,hellS,hSleK,hEledger,
      hcapacityLedger,hq,hD,hzero,hpos,hleaf,hK,hrouting,?_⟩
    · intro Q
      refine ⟨ht Q,hcap Q,?_⟩
      exact Nat.sub_le _ _
    · intro Q hQ
      exact ⟨hhzero Q hQ,hszero Q hQ,hdsat Q hQ⟩
    · intro σ hσ hbase hfix
      have habs := actual_capacity_port_parity_absorption
        (Fin a × Fin b) ER rs rd r K σ (fun e => e.property.1)
        hzero hpos hleaf hσ hbase hfix hK
      refine ⟨habs,?_⟩
      have hbound : (R : ℤ) + (K : ℤ) ≥
          3 * ((C : ℤ) - (R : ℤ)) + 4 * (bCount rs rd r σ hσ : ℤ) +
          2 * (cCount rs rd r σ hσ : ℤ) + (oddLLCount rs rd r σ hσ : ℤ) :=
        habs.2.2.2.2.1
      have hledgerZ := congrArg (fun n : ℕ => (n : ℤ)) hcapacityLedger
      have hEKZ := congrArg (fun n : ℕ => (n : ℤ)) hEK
      dsimp only [H] at hledgerZ
      push_cast at hledgerZ hEKZ
      nlinarith
  refine ⟨hbudget,hzero,hpos,hleafS,?_,hellS,hEledger⟩
  intro e he
  have hsrcpos : 0 < degree rs rd (rs e) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨(e,false),rfl⟩⟩
  have hdstpos : 0 < degree rs rd (rd e) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨(e,true),rfl⟩⟩
  have hsData := hZeroData (rs e) he.1 hsrcpos
  have hdData := hZeroData (rd e) he.2 hdstpos
  obtain ⟨i,hi⟩ := (hfibre (rs e) (src e.val)).mp rfl
  obtain ⟨j,hj⟩ := (hfibre (rd e) (dst e.val)).mp rfl
  have hiP : i ∈ pCorners (rs e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(e.val,false),hi.symm⟩
  have hjP : j ∈ pCorners (rd e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(e.val,true),hj.symm⟩
  have hiS := hResidualNotAttach e false (rs e) i hi.symm
  have hjS := hResidualNotAttach e true (rd e) j hj.symm
  have hseam : squareGrid.Adj ((corner (rs e) i).1.val, (corner (rs e) i).2.val)
      ((corner (rd e) j).1.val, (corner (rd e) j).2.val) := by
    simpa only [hi,hj] using hadj e.val
  have hpatternFinite : ∀ (U : Finset (Fin 2 × Fin 2)) (c : Fin 2 × Fin 2),
      U.card = 2 → c ∉ U →
      (∀ u ∈ U, ∀ v ∈ insert c U, ∀ w ∈ insert c U, v ≠ w →
        ((u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.2 = v.2 ∧ u.1 ≠ v.1)) →
        ((u.1 = w.1 ∧ u.2 ≠ w.2) ∨ (u.2 = w.2 ∧ u.1 ≠ w.1)) → False) →
      ∀ v, ((c.1 = v.1 ∧ c.2 ≠ v.2) ∨ (c.2 = v.2 ∧ c.1 ≠ v.1)) → v ∈ U := by
    clear * - hfourCount
    intro U c hc hn ht v hv
    have hcount := hfourCount U
    have hb00 := fun hu hv hw => ht (0,0) hu (0,1) hv (1,0) hw (by decide) (by decide) (by decide)
    have hb01 := fun hu hv hw => ht (0,1) hu (0,0) hv (1,1) hw (by decide) (by decide) (by decide)
    have hb10 := fun hu hv hw => ht (1,0) hu (0,0) hv (1,1) hw (by decide) (by decide) (by decide)
    have hb11 := fun hu hv hw => ht (1,1) hu (0,1) hv (1,0) hw (by decide) (by decide) (by decide)
    rcases c with ⟨c0,c1⟩
    rcases v with ⟨v0,v1⟩
    fin_cases c0 <;> fin_cases c1 <;> fin_cases v0 <;> fin_cases v1
    all_goals simp only [Prod.mk.injEq, Fin.reduceEq, and_true, true_and,
      false_and, and_false, or_false, false_or] at hv
    all_goals try contradiction
    all_goals by_contra hnv
    all_goals split_ifs at hcount <;> simp_all
  have hpattern : ∀ Q c, t Q + s Q = 2 →
      c ∈ pCorners Q → c ∉ sCorners Q →
      ∀ v, ((c.1 = v.1 ∧ c.2 ≠ v.2) ∨ (c.2 = v.2 ∧ c.1 ≠ v.1)) →
        corner Q v ∈ T ∨ v ∈ sCorners Q := by
    intro Q c hts hcP hcS
    let U := tCorners Q ∪ sCorners Q
    have hdisj : Disjoint (tCorners Q) (sCorners Q) :=
      (htpDisjoint Q).mono_right (fun v hv => (hsCorner Q v hv).1)
    have hUc : U.card = 2 := by
      rw [Finset.card_union_of_disjoint hdisj, htCount, hsCount]
      exact hts
    have hcU : c ∉ U := by
      intro hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact (hpCorner Q c hcP).2 (Finset.mem_filter.mp hc).2
      · exact hcS hc
    have hWA : ∀ v ∈ insert c U, corner Q v ∈ A := by
      intro v hv
      rcases Finset.mem_insert.mp hv with heq | hv
      · rw [heq]
        exact (hpCorner Q c hcP).1
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact hTA (Finset.mem_filter.mp hv).2
        · exact (hpCorner Q v (hsCorner Q v hv).1).1
    intro v hv
    have hvU := hpatternFinite U c hUc hcU (by
      intro u hu v hv w hw hvw huv huw
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hbad Q u v w hvw huv huw (Finset.mem_filter.mp hu).2
          (hWA v hv) (hWA w hw)
      · obtain ⟨_,z,huz,hz⟩ := hsCorner Q u hu
        rcases hNeighborCover u v w z hvw huv huw huz with heq | heq
        · exact hz (heq.symm ▸ hWA v hv)
        · exact hz (heq.symm ▸ hWA w hw)) v hv
    rcases Finset.mem_union.mp hvU with hvU | hvU
    · exact Or.inl (Finset.mem_filter.mp hvU).2
    · exact Or.inr hvU
  have hraw : ∀ Q k, k ∈ sCorners Q →
      ∃ x : Fin (2 * a) × Fin (2 * b), κ x ≠ Q ∧ t (κ x) = 2 ∧
        x ∈ A ∧ x ∉ T ∧ squareGrid.Adj (x.1.val,x.2.val)
          ((corner Q k).1.val,(corner Q k).2.val) := by
    intro Q k hk
    obtain ⟨f,hf,hfk⟩ := (Finset.mem_filter.mp hk).2
    rcases hf with ⟨hs,hd,htd⟩ | ⟨hd,hs,hts⟩
    · have hfk' : src f = corner Q k := by simpa only [receive,if_pos hs] using hfk
      exact ⟨dst f,hd,htd,(hPA f).2,(hdisjoint f).2,by simpa only [hfk'] using (hadj f).symm⟩
    · have hfk' : dst f = corner Q k := by simpa only [receive,if_neg hs] using hfk
      exact ⟨src f,hs,hts,(hPA f).1,(hdisjoint f).1,by simpa only [hfk'] using hadj f⟩
  have hforced : ∀ Q c k x, corner Q c ∈ A →
      ((c.1 = k.1 ∧ c.2 ≠ k.2) ∨ (c.2 = k.2 ∧ c.1 ≠ k.1)) →
      κ x ≠ Q → t (κ x) = 2 → x ∈ A → x ∉ T →
      squareGrid.Adj (x.1.val,x.2.val) ((corner Q k).1.val,(corner Q k).2.val) →
      (c.1 = k.1 ∧ x.1.val = (corner Q k).1.val) ∨
      (c.2 = k.2 ∧ x.2.val = (corner Q k).2.val) := by
    intro Q c k x hc hck hne hs hx hn hxy
    obtain ⟨u,hu⟩ := (hfibre (κ x) x).mp rfl
    obtain ⟨z,w,hz,hzQ,hwQ,hxz,hkw,hzw,hwA⟩ :=
      hblank (κ x) Q u k hne (by simpa only [hu] using hxy)
        hs (by simpa only [hu] using hx) (by simpa only [hu] using hn)
    obtain ⟨v,hv⟩ := (hfibre (κ x) z).mp hzQ
    obtain ⟨l,hl⟩ := (hfibre Q w).mp hwQ
    have hlc : l ≠ c := by
      intro heq
      exact hwA (by simpa only [← hl,heq] using hc)
    have hnQ : (κ x).1.val ≠ Q.1.val ∨ (κ x).2.val ≠ Q.2.val := by
      by_contra heq
      push Not at heq
      exact hne (Prod.ext (Fin.ext heq.1) (Fin.ext heq.2))
    have hnl : l.1.val ≠ c.1.val ∨ l.2.val ≠ c.2.val := by
      by_contra heq
      push Not at heq
      exact hlc (Prod.ext (Fin.ext heq.1) (Fin.ext heq.2))
    have hu0 := u.1.isLt
    have hu1 := u.2.isLt
    have hv0 := v.1.isLt
    have hv1 := v.2.isLt
    have hl0 := l.1.isLt
    have hl1 := l.2.isLt
    have hc0 := c.1.isLt
    have hc1 := c.2.isLt
    have hk0 := k.1.isLt
    have hk1 := k.2.isLt
    rw [← hu] at hxy ⊢
    rw [← hv] at hxz hzw
    rw [← hl] at hkw hzw
    simp only [Fin.ext_iff] at hck ⊢
    dsimp only [squareGrid,corner] at hxy hxz hkw hzw ⊢
    clear * - hnQ hnl hu0 hu1 hv0 hv1 hl0 hl1 hc0 hc1 hk0 hk1 hxy hxz hkw hzw hck
    clear_value κ
    omega
  let k : Fin 2 × Fin 2 := if (corner (rs e) i).1.val = (corner (rd e) j).1.val
    then (flip i.1,i.2) else (i.1,flip i.2)
  let l : Fin 2 × Fin 2 := if (corner (rs e) i).1.val = (corner (rd e) j).1.val
    then (flip j.1,j.2) else (j.1,flip j.2)
  have hik : (i.1 = k.1 ∧ i.2 ≠ k.2) ∨ (i.2 = k.2 ∧ i.1 ≠ k.1) := by
    dsimp only [k]
    split_ifs
    · exact Or.inr ⟨rfl,(hflipne _).symm⟩
    · exact Or.inl ⟨rfl,(hflipne _).symm⟩
  have hjl : (j.1 = l.1 ∧ j.2 ≠ l.2) ∨ (j.2 = l.2 ∧ j.1 ≠ l.1) := by
    dsimp only [l]
    split_ifs
    · exact Or.inr ⟨rfl,(hflipne _).symm⟩
    · exact Or.inl ⟨rfl,(hflipne _).symm⟩
  have hkl : squareGrid.Adj ((corner (rs e) k).1.val,(corner (rs e) k).2.val)
      ((corner (rd e) l).1.val,(corner (rd e) l).2.val) := by
    have hi0 := i.1.isLt
    have hi1 := i.2.isLt
    have hj0 := j.1.isLt
    have hj1 := j.2.isLt
    dsimp only [k,l]
    split_ifs with hr
    all_goals dsimp only [squareGrid,corner,flip] at hr hseam ⊢
    all_goals clear * - hr hseam hi0 hi1 hj0 hj1
    all_goals clear_value rs rd
    all_goals omega
  have hkU := hpattern (rs e) i hsData.2.2.1 hiP hiS k hik
  have hlU := hpattern (rd e) j hdData.2.2.1 hjP hjS l hjl
  have hkA : corner (rs e) k ∈ A := hkU.elim (fun ht => hTA ht) (fun hs => (hpCorner _ _ (hsCorner _ _ hs).1).1)
  have hlA : corner (rd e) l ∈ A := hlU.elim (fun ht => hTA ht) (fun hs => (hpCorner _ _ (hsCorner _ _ hs).1).1)
  have hkS : k ∈ sCorners (rs e) := by
    rcases hkU with hkT | hkS
    · have heq := congrArg κ (htwo _ hkT (corner (rs e) i) (corner (rd e) l)
        (hpCorner _ _ hiP).1 hlA ((hcorneradj _ _ _).mpr hik).symm hkl)
      rw [hcorner,hcorner] at heq
      exact False.elim (e.property.1 heq)
    · exact hkS
  have hlS : l ∈ sCorners (rd e) := by
    rcases hlU with hlT | hlS
    · have heq := congrArg κ (htwo _ hlT (corner (rd e) j) (corner (rs e) k)
        (hpCorner _ _ hjP).1 hkA ((hcorneradj _ _ _).mpr hjl).symm hkl.symm)
      rw [hcorner,hcorner] at heq
      exact False.elim (e.property.1 heq.symm)
    · exact hlS
  obtain ⟨x,hxQ,hx2,hxA,hxT,hxk⟩ := hraw (rs e) k hkS
  obtain ⟨y,hyQ,hy2,hyA,hyT,hyl⟩ := hraw (rd e) l hlS
  have hxdir := hforced (rs e) i k x (hpCorner _ _ hiP).1 hik hxQ hx2 hxA hxT hxk
  have hydir := hforced (rd e) j l y (hpCorner _ _ hjP).1 hjl hyQ hy2 hyA hyT hyl
  have hxy : squareGrid.Adj (x.1.val,x.2.val) (y.1.val,y.2.val) := by
    have hi0 := i.1.isLt
    have hi1 := i.2.isLt
    have hj0 := j.1.isLt
    have hj1 := j.2.isLt
    have hxN : x.1.val / 2 ≠ (rs e).1.val ∨ x.2.val / 2 ≠ (rs e).2.val := by
      by_contra hn
      push Not at hn
      exact hxQ (Prod.ext (Fin.ext hn.1) (Fin.ext hn.2))
    have hyN : y.1.val / 2 ≠ (rd e).1.val ∨ y.2.val / 2 ≠ (rd e).2.val := by
      by_contra hn
      push Not at hn
      exact hyQ (Prod.ext (Fin.ext hn.1) (Fin.ext hn.2))
    dsimp only [k,l] at hxdir hydir hxk hyl
    split_ifs at hxdir hydir hxk hyl with hr
    all_goals simp only [Fin.ext_iff] at hxdir hydir
    all_goals dsimp only [squareGrid,corner,flip] at hr hseam hxdir hydir hxk hyl ⊢
    all_goals clear * - hxN hyN hxdir hydir hxk hyl hseam hr hi0 hi1 hj0 hj1
    all_goals clear_value rs rd
    all_goals omega
  have hxyQ : κ x ≠ κ y := by
    intro hsame
    have hxdir' := hxdir
    have hydir' := hydir
    have he1 := congrArg (fun Q : Fin a × Fin b => Q.1.val) hsame
    have he2 := congrArg (fun Q : Fin a × Fin b => Q.2.val) hsame
    have hi0 := i.1.isLt
    have hi1 := i.2.isLt
    have hj0 := j.1.isLt
    have hj1 := j.2.isLt
    have hQ : (rs e).1.val ≠ (rd e).1.val ∨ (rs e).2.val ≠ (rd e).2.val := by
      by_contra hn
      push Not at hn
      exact e.property.1 (Prod.ext (Fin.ext hn.1) (Fin.ext hn.2))
    dsimp only [k,l] at hxdir' hydir'
    split_ifs at hxdir' hydir' with hr
    all_goals simp only [Fin.ext_iff] at hxdir' hydir'
    all_goals dsimp only [κ,squareGrid,corner,flip] at he1 he2 hr hseam hxdir' hydir'
    all_goals clear * - he1 he2 hr hseam hxdir' hydir' hQ hi0 hi1 hj0 hj1
    all_goals clear_value rs rd
    all_goals omega
  exact hsatsep x y hxyQ hxy hx2 hy2 hxA hxT hyA hyT

#print axioms actual_even_rectangular_residual_bridge

end
end D5.S3.Combinatorics.Graph.ActualRectangularResidualBridge
