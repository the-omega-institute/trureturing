/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedXorObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedXorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Saturated masked components restrict the parities of their two-axis XOR intersection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace

/-! Support-level consequences of signed XOR transfer for overlapping four-axis masks. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction

noncomputable section

local notation "cubeFlip" =>
  _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj flip_apply_same gamma gamma_apply IsBalanced
  IsSwitching switching_sq)
open TwoBalancedComponents (componentFinset mem_componentFinset)
open Q9ComponentSaturation (componentDefect)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MaskedGram (maskWeight)
open Q9MaskedSpectrum (maskedGraph)
open Q9SignedContactCells (parityPart)
open Q9SignedXorTransfer (maskOperator cellPart signedXorPair overlapping_mask_signed_xor)
open Q9SparseFace (maskedComponentFinset parityDefect)
open private huangMatrix cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private signed_eigen_of_singular abs_eigen mask_row mask_sq_norm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum
open private mem_maskedComponentFinset eq_off_mask parityDefect_det_eq_component from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseFace
open private parityPart_apply weighted_sum from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
open private bitPart_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer

private abbrev Vec := Q 9 → ℝ

private abbrev MaskedComponent (I : Finset (Fin 9)) (U : Finset (Q 9)) :=
  ((maskedGraph I).induce (U : Set (Q 9))).ConnectedComponent

private theorem full_component (I : Finset (Fin 9)) (U : Finset (Q 9))
    (C : MaskedComponent I U) :
    let S := maskedComponentFinset I U C
    ∃ D : ((hypercube 9).induce (S : Set (Q 9))).ConnectedComponent,
      componentFinset S D = S := by
  let S := maskedComponentFinset I U C
  let H := (hypercube 9).induce (S : Set (Q 9))
  let φ : C.toSimpleGraph →g H :=
    { toFun := fun v => ⟨v.val.val, (mem_maskedComponentFinset I U C _).mpr
        ⟨v.val.property, v.property⟩⟩
      map_rel' := by
        intro v w h
        obtain ⟨i, _, hi⟩ := (show (maskedGraph I).Adj v.val.val w.val.val from h)
        exact show (hypercube 9).Adj v.val.val w.val.val from hi ▸ flip_adj v.val.val i }
  obtain ⟨r, hr⟩ := C.nonempty_supp
  let base : C := ⟨r, hr⟩
  refine ⟨H.connectedComponentMk (φ base), Finset.Subset.antisymm ?_ ?_⟩
  · exact TwoBalancedComponents.componentFinset_subset _ _
  · intro x hx
    obtain ⟨hxU, hxC⟩ := (mem_maskedComponentFinset I U C x).mp hx
    let v : C := ⟨⟨x, hxU⟩, hxC⟩
    have h := (C.connected_toSimpleGraph.preconnected v base).map φ
    exact (mem_componentFinset S _ x).mpr ⟨hx, SimpleGraph.ConnectedComponent.sound h⟩

set_option maxHeartbeats 600000 in
-- The ambient norm comparison uses sums over the full nine-cube.
private theorem switched_eigen (I : Finset (Fin 9)) (U : Finset (Q 9))
    (C : MaskedComponent I U) (p : Bool) (hI : I.Nonempty)
    {s : Vec} (hs : IsSwitching U s)
    (hdet : (parityDefect (maskWeight I) (maskedComponentFinset I U C) p).det = 0) :
    let S := maskedComponentFinset I U C
    ∃ z : Vec, (∀ x ∉ S, z x = 0) ∧ (∀ x ∈ S, 0 < s x * z x) ∧
      maskOperator I z = Real.sqrt (I.card : ℝ) • z := by
  classical
  let S := maskedComponentFinset I U C
  have subU : S ⊆ U := fun x hx => ((mem_maskedComponentFinset I U C x).mp hx).choose
  have hsS : IsSwitching S s :=
    ⟨fun x hx => hs.1 x (subU hx), fun x hx y hy => hs.2 x (subU hx) y (subU hy)⟩
  obtain ⟨D, hD⟩ := full_component I U C
  change componentFinset S D = S at hD
  have detD : (componentDefect (maskWeight I) S p D).det = 0 := by
    rw [← parityDefect_det_eq_component, hD]
    exact hdet
  obtain ⟨z, hne, hzero, he⟩ := signed_eigen_of_singular S p D I hI detD
  rw [hD] at hzero
  let lam := Real.sqrt (I.card : ℝ)
  have hrow := abs_eigen I S ⟨s, hsS⟩ hzero he
  obtain ⟨r, hr⟩ : ∃ x, z x ≠ 0 := by
    by_contra! hz
    exact hne (funext hz)
  have hrS : r ∈ S := by by_contra h; exact hr (hzero r h)
  obtain ⟨hrU, hrC⟩ := (mem_maskedComponentFinset I U C r).mp hrS
  let base : (U : Set (Q 9)) := ⟨r, hrU⟩
  have hpos (x : Q 9) (hx : x ∈ S) : 0 < |z x| := by
    obtain ⟨hxU, hxC⟩ := (mem_maskedComponentFinset I U C x).mp hx
    let v : (U : Set (Q 9)) := ⟨x, hxU⟩
    let H := (maskedGraph I).induce (U : Set (Q 9))
    have hrx : H.Reachable base v := C.reachable_of_mem_supp hrC hxC
    have walk_pos {w : (U : Set (Q 9))} (hw : Relation.ReflTransGen H.Adj base w) :
        w ∈ C.supp ∧ 0 < |z w.val| := by
      induction hw with
      | refl => exact ⟨hrC, abs_pos.mpr hr⟩
      | @tail u w _ hadj ih =>
        have hwC := C.mem_supp_of_adj_mem_supp ih.1 hadj
        have hwS := (mem_maskedComponentFinset I U C _).mpr ⟨w.property, hwC⟩
        have huS := (mem_maskedComponentFinset I U C _).mpr ⟨u.property, ih.1⟩
        have hmem : u.val ∈ S.filter ((maskedGraph I).Adj w.val) :=
          Finset.mem_filter.mpr ⟨huS, hadj.symm⟩
        have hle := Finset.single_le_sum (f := fun y => |z y|)
          (fun y _ => abs_nonneg (z y)) hmem
        rw [hrow w.val hwS] at hle
        exact ⟨hwC, pos_of_mul_pos_right (ih.2.trans_le hle) (Real.sqrt_nonneg _)⟩
    exact (walk_pos ((SimpleGraph.reachable_iff_reflTransGen base v).mp hrx)).2
  let f : Vec := fun x => s x * |z x|
  have hfzero (x : Q 9) (hx : x ∉ S) : f x = 0 := by simp [f, hzero x hx]
  have hswitch (x : Q 9) (hx : x ∈ S) : s x * f x = |z x| := by
    rw [show f x = s x * |z x| from rfl, ← mul_assoc, ← pow_two, switching_sq hsS hx, one_mul]
  have heOn (x : Q 9) (hx : x ∈ S) :
      weightedLinear (maskWeight I) f x = lam * f x := by
    have h := mask_row I S hsS hfzero hx
    have hsum : ∑ y ∈ S.filter ((maskedGraph I).Adj x), s y * f y =
        ∑ y ∈ S.filter ((maskedGraph I).Adj x), |z y| :=
      Finset.sum_congr rfl fun y hy => hswitch y (Finset.mem_filter.mp hy).1
    rw [hsum, hrow x hx, ← hswitch x hx] at h
    have hsne : s x ≠ 0 := by rcases hsS.1 x hx with h | h <;> simp [h]
    apply mul_left_cancel₀ hsne
    rw [mul_left_comm (s x) lam]
    exact h
  have hshell : ∑ x ∈ Finset.univ \ S, (weightedLinear (maskWeight I) f x) ^ 2 = 0 := by
    have h := Finset.sum_sdiff
      (f := fun x => (weightedLinear (maskWeight I) f x) ^ 2) (Finset.subset_univ S)
    have hinside : ∑ x ∈ S, (weightedLinear (maskWeight I) f x) ^ 2 =
        (I.card : ℝ) * ∑ x, f x ^ 2 := by
      calc
        _ = ∑ x ∈ S, (lam * f x) ^ 2 :=
          Finset.sum_congr rfl fun x hx => by rw [heOn x hx]
        _ = _ := by
          simp only [mul_pow, ← Finset.mul_sum, lam,
            Real.sq_sqrt (by positivity : 0 ≤ (I.card : ℝ))]
          rw [Finset.sum_subset (Finset.subset_univ S)]
          intro x _ hx
          simp [hfzero x hx]
    rw [hinside, mask_sq_norm] at h
    linarith
  refine ⟨f, hfzero, fun x hx => (hswitch x hx).symm ▸ hpos x hx, ?_⟩
  funext x
  change weightedLinear (maskWeight I) f x = lam * f x
  by_cases hx : x ∈ S
  · exact heOn x hx
  · rw [hfzero x hx, mul_zero]
    exact eq_zero_of_pow_eq_zero
      ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hshell x
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩))

private theorem mask_sum (I : Finset (Fin 9)) (f : Vec) :
    maskOperator I f = ∑ i ∈ I, gamma i f := by
  classical
  simp only [maskOperator, weighted_sum, maskWeight, ite_smul, one_smul, zero_smul]
  rw [← Finset.sum_filter]
  simp

private theorem mask_insert {I : Finset (Fin 9)} {a : Fin 9} (ha : a ∉ I) (f : Vec) :
    maskOperator (insert a I) f = maskOperator I f + gamma a f := by
  rw [mask_sum, mask_sum, Finset.sum_insert ha, add_comm]

private theorem mem_across_mask {I : Finset (Fin 9)} {U : Finset (Q 9)}
    {C : MaskedComponent I U} {x y : Q 9}
    (hx : x ∈ maskedComponentFinset I U C) (hy : y ∈ U)
    (h : (maskedGraph I).Adj x y) : y ∈ maskedComponentFinset I U C := by
  obtain ⟨hxU, hxC⟩ := (mem_maskedComponentFinset I U C x).mp hx
  exact (mem_maskedComponentFinset I U C y).mpr ⟨hy, C.mem_supp_of_adj_mem_supp hxC h⟩

private theorem cell_apply (a b : Fin 9) (p q : Bool) (f : Vec) (x : Q 9) :
    cellPart a b p q f x = if x a = p ∧ x b = q then f x else 0 := by
  by_cases ha : x a = p <;> by_cases hb : x b = q <;>
    simp [cellPart, bitPart_apply, ha, hb]

private theorem parity_flip (x : Q 9) (i : Fin 9) :
    parity (cubeFlip x i) = !parity x := by
  have h := cubeParity_ne_of_adj (flip_adj x i)
  change parity x ≠ parity (cubeFlip x i) at h
  cases hx : parity x <;> cases hy : parity (cubeFlip x i) <;> simp_all

private theorem flip_ne (x : Q 9) {i j : Fin 9} (h : j ≠ i) : cubeFlip x i j = x j := by
  simp [BalancedCriticalSpectrum.flip, h]

private theorem common_term_zero {U : Finset (Q 9)} {I : Finset (Fin 9)} {a b : Fin 9}
    {C : MaskedComponent (insert a I) U} {E : MaskedComponent (insert b I) U}
    {f g : Vec} (hf : ∀ x ∉ maskedComponentFinset (insert a I) U C, f x = 0)
    (hg : ∀ x ∉ maskedComponentFinset (insert b I) U E, g x = 0)
    (hind : ∀ x ∈ maskedComponentFinset (insert a I) U C ∩ maskedComponentFinset (insert b I) U E,
      ∀ i ∈ I, cubeFlip x i ∉ maskedComponentFinset (insert a I) U C ∩
        maskedComponentFinset (insert b I) U E) :
    f ⬝ᵥ maskOperator I g = 0 := by
  rw [dotProduct, mask_sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ maskedComponentFinset (insert a I) U C
  · suffices h : (∑ i ∈ I, gamma i g) x = 0 by rw [h, mul_zero]
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [gamma_apply]
    suffices hy : cubeFlip x i ∉ maskedComponentFinset (insert b I) U E by rw [hg _ hy, mul_zero]
    intro hy
    have hxU := ((mem_maskedComponentFinset _ U C x).mp hx).choose
    have hyU := ((mem_maskedComponentFinset _ U E _).mp hy).choose
    have hadj (j : Fin 9) : (maskedGraph (insert j I)).Adj x (cubeFlip x i) :=
      ⟨i, Finset.mem_insert_of_mem hi, rfl⟩
    have hyC := mem_across_mask hx hyU (hadj a)
    have hxE := mem_across_mask hy hxU (hadj b).symm
    exact hind x (Finset.mem_inter.mpr ⟨hx, hxE⟩) i hi (Finset.mem_inter.mpr ⟨hyC, hy⟩)
  · rw [hf x hx, zero_mul]

set_option maxHeartbeats 900000 in
-- The transfer compares three kinds of parity-filtered dot products.
open Classical in
/-- For two saturated masked components, disjointness forbids a singleton XOR
intersection on either parity. If their ordinary intersection is nonempty and
lies on one parity, their XOR intersection meets both parities. -/
theorem overlapping_mask_xor_intersection
    (U : Finset (Q 9)) (hU : IsBalanced U)
    (I : Finset (Fin 9)) (a b : Fin 9) (hab : a ≠ b) (hI : I.card = 3)
    (ha : a ∉ I) (hb : b ∉ I)
    (C : MaskedComponent (insert a I) U) (E : MaskedComponent (insert b I) U)
    (r s : Bool)
    (hdet :
      ((parityDefect (maskWeight (insert a I)) (maskedComponentFinset (insert a I) U C) r).det,
       (parityDefect (maskWeight (insert b I)) (maskedComponentFinset (insert b I) U E) s).det) =
      (0, 0)) :
    let F := maskedComponentFinset (insert a I) U C
    let G := maskedComponentFinset (insert b I) U E
    let X := fun t : Bool => F.filter (fun x => cubeFlip (cubeFlip x a) b ∈ G ∧ parity x = t)
    (Disjoint F G → ∀ t, (X t).card ≠ 1) ∧
    ((F ∩ G).Nonempty → (∃ t : Bool, ∀ x ∈ F ∩ G, parity x = t) → ∀ t, (X t).Nonempty) := by
  classical
  let F := maskedComponentFinset (insert a I) U C
  let G := maskedComponentFinset (insert b I) U E
  let X := fun t : Bool => F.filter (fun x => cubeFlip (cubeFlip x a) b ∈ G ∧ parity x = t)
  change (Disjoint F G → ∀ t, (X t).card ≠ 1) ∧
    ((F ∩ G).Nonempty → (∃ t : Bool, ∀ x ∈ F ∩ G, parity x = t) → ∀ t, (X t).Nonempty)
  obtain ⟨σ, hσ⟩ := hU
  have sqrt_card {i : Fin 9} (hi : i ∉ I) : Real.sqrt ((insert i I).card : ℝ) = 2 := by
    rw [Finset.card_insert_of_notMem hi, hI]
    have h : Real.sqrt (2 ^ 2 : ℝ) = 2 := Real.sqrt_sq (by norm_num)
    norm_num at h ⊢
  obtain ⟨f, hf, hfpos, hfe⟩ :=
    switched_eigen (insert a I) U C r (Finset.insert_nonempty _ _) hσ (congrArg Prod.fst hdet)
  obtain ⟨g, hg, hgpos, hge⟩ :=
    switched_eigen (insert b I) U E s (Finset.insert_nonempty _ _) hσ (congrArg Prod.snd hdet)
  rw [sqrt_card ha, mask_insert ha] at hfe
  rw [sqrt_card hb, mask_insert hb] at hge
  obtain ⟨v, hv⟩ := C.nonempty_supp
  obtain ⟨w, hw⟩ := E.nonempty_supp
  have hvF : v.val ∈ F := (mem_maskedComponentFinset _ U C _).mpr ⟨v.property, hv⟩
  have hwG : w.val ∈ G := (mem_maskedComponentFinset _ U E _).mpr ⟨w.property, hw⟩
  let p := w.val a
  let q := v.val b
  have hp (y : Q 9) (hy : y ∈ G) : y a = p :=
    eq_off_mask _ U E hy hwG (by simpa [hab] using ha)
  have hq (x : Q 9) (hx : x ∈ F) : x b = q :=
    eq_off_mask _ U C hx hvF (by simpa [hab.symm] using hb)
  let f₀ := cellPart a b p q f
  let g₀ := cellPart a b p q g
  let f₁ := cellPart a b (!p) q f
  let g₁ := cellPart a b p (!q) g
  have hf₀ (x : Q 9) (hx : x ∉ F) : f₀ x = 0 := by simp [f₀, cell_apply, hf x hx]
  have hg₀ (x : Q 9) (hx : x ∉ G) : g₀ x = 0 := by simp [g₀, cell_apply, hg x hx]
  let S := fun t : Bool => (F ∩ G).filter (fun x => parity x = t)
  let common := fun t : Bool => ∑ x ∈ S t, f x * g x
  let term := fun x : Q 9 =>
    f x * (huangMatrix 9 x (cubeFlip x a) *
      (huangMatrix 9 (cubeFlip x a) (cubeFlip (cubeFlip x a) b) * g (cubeFlip (cubeFlip x a) b)))
  let shifted := fun t : Bool => ∑ x ∈ X t, term x
  have common_eq (t : Bool) : parityPart t f₀ ⬝ᵥ parityPart t g₀ = common t := by
    have hS : S t = Finset.univ.filter (fun x => x ∈ F ∧ x ∈ G ∧ parity x = t) := by
      ext x
      simp [S, and_assoc]
    rw [dotProduct, show common t = ∑ x ∈ S t, f x * g x from rfl, hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ F
    · by_cases hy : x ∈ G
      · by_cases ht : parity x = t <;>
          simp [f₀, g₀, parityPart_apply, cell_apply, hx, hy, ht, hp x hy, hq x hx]
      · simp [hx, hy, parityPart_apply, hg₀ x hy]
    · simp [hx, parityPart_apply, hf₀ x hx]
  have shifted_eq (t : Bool) :
      signedXorPair a b (parityPart t f₁, parityPart t g₁) = shifted t := by
    have hX : X t =
        Finset.univ.filter (fun x => x ∈ F ∧ cubeFlip (cubeFlip x a) b ∈ G ∧ parity x = t) := by
      ext x
      simp [X]
    rw [signedXorPair, dotProduct, show shifted t = ∑ x ∈ X t, term x from rfl, hX,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    simp only [gamma_apply]
    let y := cubeFlip (cubeFlip x a) b
    by_cases hx : x ∈ F
    · by_cases hy : y ∈ G
      · have hya : y a = !x a := by simp only [y, flip_ne _ hab, flip_apply_same]
        have hyb : y b = !q := by simp only [y, flip_apply_same, flip_ne _ hab.symm, hq x hx]
        have hxa : x a = !p := by rw [← hp y hy, hya, Bool.not_not]
        have hyt : parity y = parity x := by simp only [y, parity_flip, Bool.not_not]
        have hpa := hp y hy
        dsimp only [y] at hy hpa hyb hyt
        by_cases ht : parity x = t <;>
          simp only [f₁, g₁, term, parityPart_apply, cell_apply, hx, hy, hxa, hq x hx,
            hpa, hyb, hyt, ht, true_and, if_true, if_false, mul_zero, zero_mul]
      · have hgz := hg y hy
        dsimp only [y] at hy hgz
        simp [g₁, parityPart_apply, cell_apply, hy, hgz]
    · simp [f₁, parityPart_apply, cell_apply, hx, hf x hx]
  have term_ne (t : Bool) {x : Q 9} (hx : x ∈ X t) : term x ≠ 0 := by
    obtain ⟨hxF, hyG, _⟩ := Finset.mem_filter.mp hx
    have hcoeff (u : Q 9) (i : Fin 9) : huangMatrix 9 u (cubeFlip u i) ≠ 0 := by
      have h := SupportedEigenSaturation.matrix_sq_of_adj (flip_adj u i)
      intro hz
      simp [hz] at h
    exact mul_ne_zero (right_ne_zero_of_mul (hfpos x hxF).ne')
      (mul_ne_zero (hcoeff _ _) (mul_ne_zero (hcoeff _ _) (right_ne_zero_of_mul (hgpos _ hyG).ne')))
  have transfer
      (hind : ∀ x ∈ F ∩ G, ∀ i ∈ I, cubeFlip x i ∉ F ∩ G) (t : Bool) :
      shifted t = 3 * common t + 4 * common (!t) := by
    have h := (overlapping_mask_signed_xor I a b hab hI ha hb p q f g hfe hge).2.2.2.1 t
    change signedXorPair a b (parityPart t f₁, parityPart t g₁) =
      3 * (parityPart t f₀ ⬝ᵥ parityPart t g₀) +
      4 * (parityPart (!t) f₀ ⬝ᵥ parityPart (!t) g₀) - 2 * (f₀ ⬝ᵥ maskOperator I g₀) at h
    rw [shifted_eq, common_eq, common_eq, common_term_zero hf₀ hg₀ hind, mul_zero, sub_zero] at h
    exact h
  constructor
  · intro hdis t hcard
    have hempty : F ∩ G = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdis
    have hzero : shifted t = 0 := by
      rw [transfer (by simp [hempty])]
      simp [common, S, hempty]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
    have hxX : x ∈ X t := hx.symm ▸ Finset.mem_singleton_self x
    apply term_ne t hxX
    simpa [shifted, hx] using hzero
  · intro hne ⟨t, ht⟩ u
    have hind (x : Q 9) (hx : x ∈ F ∩ G) (i : Fin 9) (_ : i ∈ I) (hy : cubeFlip x i ∈ F ∩ G) :
        False := cubeParity_ne_of_adj (flip_adj x i) ((ht x hx).trans (ht _ hy).symm)
    have hcommonPos : 0 < common t := by
      have hS : (S t).Nonempty := by
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, ht x hx⟩⟩
      apply Finset.sum_pos _ hS
      intro x hx
      obtain ⟨hxF, hxG⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp hx).1
      have hxU := ((mem_maskedComponentFinset _ U C x).mp hxF).choose
      calc
        0 < (σ x * f x) * (σ x * g x) := mul_pos (hfpos x hxF) (hgpos x hxG)
        _ = f x * g x := by
          rw [show (σ x * f x) * (σ x * g x) = σ x ^ 2 * (f x * g x) by ring,
            switching_sq hσ hxU, one_mul]
    have hcommonZero : common (!t) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      rw [ht x (Finset.mem_filter.mp hx).1] at he
      cases t <;> simp at he
    have hshiftPos : 0 < shifted u := by
      rw [transfer hind]
      cases t <;> cases u <;> simp_all only [Bool.not_true, Bool.not_false] <;> linarith
    by_contra h
    exact hshiftPos.ne' (by simp [shifted, Finset.not_nonempty_iff_eq_empty.mp h])

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction.overlapping_mask_xor_intersection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms overlapping_mask_xor_intersection

end

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedXorObstruction
