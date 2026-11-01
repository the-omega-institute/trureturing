/- GID: D5/S3/Geometry/Polygons/PolygonStrictNormalization
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonStrictNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict normalized bounds for two complete conditioned polygon families. -/

import D5.S3.Geometry.Polygons.PolygonTraceFlip
import D5.S3.Geometry.Polygons.PolygonConditionedFan
import D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1600000

open Finset
namespace D5.S3.Geometry.Polygons.PolygonStrictNormalization
open D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual PolygonTraceFlip
open PolygonCompressionTrace PolygonSimultaneousCompression
open D5.S3.Combinatorics.SetFamily.SimultaneousCompression
variable {n : ℕ} [NeZero n]

abbrev SourceCases (P Q : Finset (ZMod n)) : Prop :=
  (P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
    (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)

private lemma sourceCases_swap {P Q : Finset (ZMod n)} (h : SourceCases P Q) : SourceCases Q P := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ <;> simp_all [SourceCases]

private lemma all_ears {P Q H : Finset (ZMod n)}
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hH : (↑H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hHE : H ⊆ E_K (P ∪ Q)) :
    (∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H, ¬Cross (ear i) (ear j)) ∧
      Disjoint H (P ∪ Q) := by
  constructor
  · intro i hi j hj
    by_cases he : i = j
    · subst j; exact not_cross_self _
    rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hj with hj | hj
    · exact hK hi hj he
    · exact fun hc => (mem_filter.mp (hHE hj)).2.2 i hi (cross_symm hc)
    · exact (mem_filter.mp (hHE hi)).2.2 j hj
    · exact hH hi hj he
  · exact disjoint_left.mpr (fun i hi hj => (mem_filter.mp (hHE hi)).2.1 hj)

private lemma actual_flip_image_shape
    (hn : 14 ≤ n) {P Q H R : Finset (ZMod n)} {h : ZMod n}
    (hE : ∀ i ∈ P ∪ Q ∪ H, ∀ j ∈ P ∪ Q ∪ H, ¬Cross (ear i) (ear j))
    (hd : Disjoint H (P ∪ Q)) (hh : h ∈ H) (hR : R ⊆ H.erase h)
    (x : ConditionFiber P Q H (insert h R)) :
    ∃ δ : Sym2 (ZMod n),
      (actual_flip_trace_map hn hE hd hh hR x).val = insert δ (x.val.erase (ear h)) := by
  rcases x with ⟨T,hT,hP,hQ,hX⟩
  exact ⟨_, rfl⟩

private lemma actual_singleton_strict
    (hn : 14 ≤ n) (P Q H : Finset (ZMod n))
    (hd : Disjoint P Q)
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : SourceCases P Q) (hHE : H ⊆ E_K (P ∪ Q))
    (hH : (↑H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (h : ZMod n) (hh : h ∈ H) : weight P Q H {h} < weight P Q H ∅ := by
  classical
  obtain ⟨hE,hDisj⟩ := all_ears hK hH hHE
  let f := actual_flip_trace_map hn hE hDisj hh (empty_subset (H.erase h))
  obtain ⟨T, hT, e, he, g, hg, heg, hed, hgd, hec, hgc⟩ :=
    (PolygonConditionedFan.source_conditioned_witnesses hn P Q hd hK hcases).2.2.2 H hHE hH h hh
  have hnot : T ∉ Set.range f := by
    rintro ⟨x,hx⟩
    obtain ⟨δ,hδ⟩ := actual_flip_image_shape hn hE hDisj hh (empty_subset (H.erase h)) x
    have hgamma : ear h ∈ x.val := by
      apply mem_earCenters.mp
      have hh' : h ∈ EarCenters x.val ∩ H := by rw [x.2.2.2.2]; simp
      exact (mem_inter.mp hh').1
    have eqδ : ∀ a ∈ T.val, Cross a (ear h) → a = δ := by
      intro a ha hc
      have ha' : a ∈ insert δ (x.val.erase (ear h)) := by
        rw [← hδ]; change a ∈ (f x).val; rw [hx]; exact ha
      rcases mem_insert.mp ha' with heq | ha'
      · exact heq
      · exact (x.2.1.noncrossing a (mem_of_mem_erase ha') (ear h) hgamma hc).elim
    exact heg ((eqδ e he hec).trans (eqδ g hg hgc).symm)
  have hc := Fintype.card_lt_of_injective_of_notMem f
    (actual_flip_trace_injective hn hE hDisj hh (empty_subset (H.erase h))) hnot
  simpa only [weight, Nat.card_eq_fintype_card, insert_empty_eq] using
    (show (Fintype.card (ConditionFiber P Q H {h}) : ℝ) <
      Fintype.card (ConditionFiber P Q H ∅) from by exact_mod_cast hc)

private lemma actual_weight_antitone
    (hn : 14 ≤ n) (P Q H : Finset (ZMod n))
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hHE : H ⊆ E_K (P ∪ Q))
    (hH : (↑H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j))) :
    ∀ R ⊆ H, ∀ S ⊆ H, R ⊆ S → weight P Q H S ≤ weight P Q H R := by
  classical
  obtain ⟨hE,hDisj⟩ := all_ears hK hH hHE
  have step (h : ZMod n) (hh : h ∈ H) (R : Finset (ZMod n)) (hR : R ⊆ H.erase h) :
      weight P Q H (insert h R) ≤ weight P Q H R := by
    unfold weight
    exact_mod_cast (show Nat.card (ConditionFiber P Q H (insert h R)) ≤
      Nat.card (ConditionFiber P Q H R) from by
        simpa only [Nat.card_eq_fintype_card] using actual_flip_trace_card_le hn hE hDisj hh hR)
  have general : ∀ D : Finset (ZMod n), ∀ X ⊆ H, D ⊆ H → Disjoint D X →
      weight P Q H (D ∪ X) ≤ weight P Q H X := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro X hX _ _; simp
    | @insert d D hd ihD =>
      intro X hX hDH hDX
      have hdH := hDH (mem_insert_self d D)
      have hDX' : Disjoint D X := disjoint_of_subset_left (subset_insert d D) hDX
      have hDsub : D ⊆ H := fun i hi => hDH (mem_insert_of_mem hi)
      have hdnot : d ∉ D ∪ X := by
        simp only [mem_union, not_or]; exact ⟨hd, disjoint_left.mp hDX (mem_insert_self _ _)⟩
      have hsub' : D ∪ X ⊆ H.erase d := by
        intro i hi; exact mem_erase.mpr ⟨fun he => hdnot (he ▸ hi), (union_subset hDsub hX) hi⟩
      simpa only [insert_union] using (step d hdH (D ∪ X) hsub').trans (ihD X hX hDsub hDX')
  intro R hR S hS hRS
  have heq : (S \ R) ∪ R = S := sdiff_union_of_subset hRS
  rw [← heq]
  exact general _ R hR (sdiff_subset.trans hS) sdiff_disjoint

private noncomputable def tracePartition (P Q H : Finset (ZMod n)) :
    WholeFiber P Q ≃ (Σ R : {R // R ∈ H.powerset}, ConditionFiber P Q H R.val) :=
  (Equiv.sigmaSubtypeFiberEquiv
    (fun T : WholeFiber P Q => EarCenters T.val ∩ H)
    (fun R => R ∈ H.powerset)
    (fun _ => mem_powerset.mpr inter_subset_right)).symm.trans
    (Equiv.sigmaCongrRight fun R =>
      { toFun := fun T => ⟨T.val.val, T.val.2.1, T.val.2.2.1, T.val.2.2.2.1, T.2⟩
        invFun := fun T => ⟨⟨T.val, T.2.1, T.2.2.1, T.2.2.2.1, by simp⟩, T.2.2.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })

private lemma actual_partition_total (P Q H : Finset (ZMod n)) :
    mass (weight P Q H) H.powerset = (Nat.card (WholeFiber P Q) : ℝ) := by
  classical
  have hc := Nat.card_congr (tracePartition P Q H)
  rw [Nat.card_sigma] at hc
  unfold mass weight
  rw [hc, Nat.cast_sum]
  exact (Finset.sum_attach _ _).symm

section FKG
variable {β : Type*} [Fintype β] [DistribLattice β] [OrderBot β]

private lemma uniform_upper_mass (w : β → ℝ) (hw : Antitone w) (C : Finset β)
    (hC : ∀ a ∈ C, ∀ b, a ≤ b → b ∈ C) :
    (Fintype.card β : ℝ) * (∑ a ∈ C, w a) ≤ (∑ a, w a) * C.card := by
  classical
  let f : β → ℝ := fun a => w ⊥ - w a
  let g : β → ℝ := fun a => if a ∈ C then 1 else 0
  have hf : Monotone f := fun a b hab => sub_le_sub_left (hw hab) _
  have hg : Monotone g := by
    intro a b hab
    by_cases ha : a ∈ C
    · simp [g, ha, hC a ha b hab]
    · simp [g, ha]; split_ifs <;> norm_num
  have h := fkg (μ := fun _ : β => (1 : ℝ)) (f := f) (g := g)
    (by intro a; norm_num) (by intro a; exact sub_nonneg.mpr (hw bot_le))
    (by intro a; dsimp [g]; split_ifs <;> norm_num) hf hg (by intros; norm_num)
  have hfSum : (∑ a, f a) = (Fintype.card β : ℝ) * w ⊥ - ∑ a, w a := by
    simp [f, sum_sub_distrib, mul_comm]
  have hgSum : (∑ a, g a) = (C.card : ℝ) := by simp [g]
  have hfgSum : (∑ a, f a * g a) = (C.card : ℝ) * w ⊥ - ∑ a ∈ C, w a := by
    simp [g, f, mul_ite, sum_sub_distrib, mul_comm]
  simp only [one_mul] at h
  rw [hfSum, hgSum, hfgSum] at h
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  nlinarith

private lemma strict_uniform_upper_mass (w : β → ℝ) (hw : Antitone w)
    (hgap : ∀ a : β, a ≠ ⊥ → w a + 1 ≤ w ⊥)
    (C : Finset β) (hC : ∀ a ∈ C, ∀ b, a ≤ b → b ∈ C)
    (hne : C.Nonempty) (hbot : ⊥ ∉ C) (htotal : 0 < ∑ a, w a) :
    (∑ a ∈ C, w a) / (∑ a, w a) < (C.card : ℝ) / Fintype.card β := by
  classical
  let u : β → ℝ := fun a => w a - if a = ⊥ then 1 else 0
  have hu : Antitone u := by
    intro a b hab
    by_cases hb : b = ⊥
    · have ha : a = ⊥ := le_antisymm (hb ▸ hab) bot_le
      simp [ha,hb]
    by_cases ha : a = ⊥
    · simp only [u, ha, hb, if_true, if_false, sub_zero]
      linarith [hgap b hb]
    · simp only [u, ha, hb, if_false, sub_zero]
      exact hw hab
  have hs : (∑ a, u a) = (∑ a, w a) - 1 := by simp [u, sum_sub_distrib]
  have hsc : (∑ a ∈ C, u a) = ∑ a ∈ C, w a := by
    apply sum_congr rfl
    intro a ha
    have han : a ≠ ⊥ := fun he => hbot (he ▸ ha)
    simp [u,han]
  have h := uniform_upper_mass u hu C hC
  rw [hs,hsc] at h
  have hc : (0 : ℝ) < C.card := by exact_mod_cast card_pos.mpr hne
  have hb : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty β from ⟨⊥⟩)
  apply (div_lt_div_iff₀ htotal hb).mpr
  nlinarith
end FKG

private lemma actual_nonsingleton_gap
    (hn : 14 ≤ n) (P Q H : Finset (ZMod n))
    (hd : Disjoint P Q)
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : SourceCases P Q) (hHE : H ⊆ E_K (P ∪ Q))
    (hH : (↑H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j))) :
    ∀ R ⊆ H, R ≠ ∅ → weight P Q H R + 1 ≤ weight P Q H ∅ := by
  classical
  intro R hRH hR
  obtain ⟨h,hh⟩ := nonempty_iff_ne_empty.mpr hR
  have hs := actual_singleton_strict hn P Q H hd hK hcases hHE hH h (hRH hh)
  have ha := actual_weight_antitone hn P Q H hK hHE hH {h}
    (singleton_subset_iff.mpr (hRH hh)) R hRH (singleton_subset_iff.mpr hh)
  unfold weight at hs ha ⊢
  have hnlt : Nat.card (ConditionFiber P Q H {h}) < Nat.card (ConditionFiber P Q H ∅) := by
    exact_mod_cast hs
  have hnle : Nat.card (ConditionFiber P Q H R) ≤ Nat.card (ConditionFiber P Q H {h}) := by
    exact_mod_cast ha
  have : Nat.card (ConditionFiber P Q H R) + 1 ≤ Nat.card (ConditionFiber P Q H ∅) := by omega
  exact_mod_cast this

private abbrev TraceLattice (H : Finset (ZMod n)) := Set.Iic H

private noncomputable def liftFamily (H : Finset (ZMod n)) (C : Finset (Finset (ZMod n))) :
    Finset (TraceLattice H) := by
  classical
  exact univ.filter (fun X => X.val ∈ C)

private lemma mem_liftFamily (H : Finset (ZMod n)) (C : Finset (Finset (ZMod n)))
    (X : TraceLattice H) : X ∈ liftFamily H C ↔ X.val ∈ C := by
  classical
  simp [liftFamily]

private lemma lifted_sum (H : Finset (ZMod n)) (C : Finset (Finset (ZMod n)))
    (hCH : C ⊆ H.powerset) (w : Finset (ZMod n) → ℝ) :
    (∑ X ∈ liftFamily H C, w X.val) = ∑ X ∈ C, w X := by
  classical
  apply sum_bij (fun X _ => X.val)
  · intro X hX; exact (mem_liftFamily H C X).mp hX
  · intro X hX Y hY he; exact Subtype.ext he
  · intro R hR
    exact ⟨⟨R,mem_powerset.mp (hCH hR)⟩, (mem_liftFamily H C _).mpr hR, rfl⟩
  · intros; rfl

private lemma lifted_card (H : Finset (ZMod n)) (C : Finset (Finset (ZMod n)))
    (hCH : C ⊆ H.powerset) : (liftFamily H C).card = C.card := by
  have h := lifted_sum H C hCH (fun _ => 1)
  simpa using h

private lemma lifted_univ (H : Finset (ZMod n)) : liftFamily H H.powerset = univ := by
  classical
  ext X
  simp only [mem_liftFamily, mem_univ, iff_true]
  exact mem_powerset.mpr X.property

private lemma actual_upper_strict
    (hn : 14 ≤ n) (P Q H : Finset (ZMod n))
    (hd : Disjoint P Q)
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : SourceCases P Q) (hHE : H ⊆ E_K (P ∪ Q))
    (hH : (↑H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (C : Finset (Finset (ZMod n))) (hCH : C ⊆ H.powerset)
    (hu : RelativelyUpper H.powerset C) (hne : C.Nonempty) (hbot : ∅ ∉ C) :
    mass (weight P Q H) C / (Nat.card (WholeFiber P Q) : ℝ) <
      (C.card : ℝ) / H.powerset.card := by
  classical
  let w : TraceLattice H → ℝ := fun X => weight P Q H X.val
  have hanti : Antitone w := by
    intro X Y hXY
    exact actual_weight_antitone hn P Q H hK hHE hH X.val X.property Y.val Y.property hXY
  have hgap : ∀ X : TraceLattice H, X ≠ ⊥ → w X + 1 ≤ w ⊥ := by
    intro X hX
    exact actual_nonsingleton_gap hn P Q H hd hK hcases hHE hH X.val X.property
      (fun he => hX (Subtype.ext he))
  have hupper : ∀ X ∈ liftFamily H C, ∀ Y, X ≤ Y → Y ∈ liftFamily H C := by
    intro X hX Y hXY
    exact (mem_liftFamily H C Y).mpr
      (hu X.val ((mem_liftFamily H C X).mp hX) Y.val (mem_powerset.mpr Y.property) hXY)
  have hne' : (liftFamily H C).Nonempty := by
    obtain ⟨R,hR⟩ := hne
    exact ⟨⟨R,mem_powerset.mp (hCH hR)⟩,(mem_liftFamily H C _).mpr hR⟩
  have hbot' : (⊥ : TraceLattice H) ∉ liftFamily H C := by
    intro hb; exact hbot ((mem_liftFamily H C _).mp hb)
  have hsum : (∑ X : TraceLattice H, w X) = (Nat.card (WholeFiber P Q) : ℝ) := by
    change (∑ X : TraceLattice H, weight P Q H X.val) = _
    rw [← lifted_univ H]
    exact (lifted_sum H H.powerset (subset_refl _) (weight P Q H)).trans (actual_partition_total P Q H)
  have htotal : 0 < ∑ X : TraceLattice H, w X := by
    rw [hsum]
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn P Q hd hK hcases).2.1
  have h := strict_uniform_upper_mass w hanti hgap (liftFamily H C) hupper hne' hbot' htotal
  rw [hsum, show (∑ X ∈ liftFamily H C, w X) = mass (weight P Q H) C from
    lifted_sum H C hCH (weight P Q H), lifted_card H C hCH] at h
  have hcard : Fintype.card (TraceLattice H) = H.powerset.card := by
    rw [← card_univ, ← lifted_univ H, lifted_card H H.powerset (subset_refl _)]
  simpa only [hcard] using h

private lemma cross_complement_card (H : Finset (ZMod n)) (C D : Finset (Finset (ZMod n)))
    (hCH : C ⊆ H.powerset) (hDH : D ⊆ H.powerset) (hc : CrossIntersecting C D) :
    C.card + D.card ≤ H.powerset.card := by
  classical
  let E := D.image (fun R => H \ R)
  have hEcard : E.card = D.card := by
    apply card_image_iff.mpr
    intro X hX Y hY he
    have h := congrArg (fun R => H \ R) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_powerset.mp (hDH hX)),
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp (hDH hY))] using h
  have hdisj : Disjoint C E := by
    apply disjoint_left.mpr
    intro X hX hXE
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hXE
    exact hc _ hX Y hY sdiff_disjoint
  have hsub : C ∪ E ⊆ H.powerset := by
    apply union_subset hCH
    intro X hX
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hX
    exact mem_powerset.mpr sdiff_subset
  have h := card_le_card hsub
  rwa [card_union_of_disjoint hdisj,hEcard] at h

lemma original_normalized_strict
    (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q)
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : SourceCases P Q)
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.val) (EarCenters U.val))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.card : ℝ) / Nat.card (WholeFiber P Q) +
      (B.card : ℝ) / Nat.card (WholeFiber Q P) < 1 := by
  classical
  have hP : P.Nonempty := card_pos.mp (by
    rcases hcases with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ <;> omega)
  have hKn : (P ∪ Q).Nonempty := hP.mono subset_union_left
  obtain ⟨H,C,D,hHE,hIndependent,hH,hCH,hDH,hCD,huC,huD,hw,hv,hnC,hnD,hnH⟩ :=
    exists_original_terminal_compression hn P Q hKn A B hc
  have hHnon : H.Nonempty := hnH hA hB
  have hHpair : (↑H : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)) :=
    fun i hi j hj _ => hH i hi j hj
  have hnotC : ∅ ∉ C := by
    intro he
    obtain ⟨Y,hY⟩ := hnD hB
    exact hCD ∅ he Y hY (by simp)
  have hnotD : ∅ ∉ D := by
    intro he
    obtain ⟨X,hX⟩ := hnC hA
    exact hCD X hX ∅ he (by simp)
  have hposP : (0 : ℝ) < Nat.card (WholeFiber P Q) := by
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn P Q hd hK hcases).2.1
  have hposQ : (0 : ℝ) < Nat.card (WholeFiber Q P) := by
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn Q P hd.symm
      (by simpa only [union_comm] using hK) (sourceCases_swap hcases)).2.1
  have hC := actual_upper_strict hn P Q H hd hK hcases hHE hHpair C hCH huC (hnC hA) hnotC
  have hD := actual_upper_strict hn Q P H hd.symm (by simpa only [union_comm] using hK)
    (sourceCases_swap hcases) (by simpa only [union_comm] using hHE) hHpair D hDH huD (hnD hB) hnotD
  have ha : (A.card : ℝ) / Nat.card (WholeFiber P Q) < (C.card : ℝ) / H.powerset.card :=
    (div_le_div_of_nonneg_right hw hposP.le).trans_lt hC
  have hb : (B.card : ℝ) / Nat.card (WholeFiber Q P) < (D.card : ℝ) / H.powerset.card :=
    (div_le_div_of_nonneg_right hv hposQ.le).trans_lt hD
  have hN : (0 : ℝ) < H.powerset.card := by
    obtain ⟨h,hh⟩ := hHnon
    exact_mod_cast card_pos.mpr (show H.powerset.Nonempty from
      ⟨{h},mem_powerset.mpr (singleton_subset_iff.mpr hh)⟩)
  have hcard : (C.card : ℝ) + D.card ≤ H.powerset.card := by
    exact_mod_cast cross_complement_card H C D hCH hDH hCD
  have hle : (C.card : ℝ) / H.powerset.card + (D.card : ℝ) / H.powerset.card ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hN).mpr hcard
  exact (add_lt_add ha hb).trans_le hle

end D5.S3.Geometry.Polygons.PolygonStrictNormalization
