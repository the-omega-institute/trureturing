/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact address supports determine native defect observation faces and acquisition bounds. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory
import D5.S3.Entropy.EntropyEquality
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout paid)
open ActualLeafHistoryRigidity (subtree)
open Geometry.NativeAncestryDefectCube (defectB defectD positions fill variant fill_at)
open Geometry.AncestorAreaInstability (T)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute execute_transfer)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open scoped symmDiff BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The six literal addresses on which a three-leaf rotation changes the reply. -/
def support (p : Address) : Finset Address :=
  {p ++ [false], p ++ [true], p ++ [false,false], p ++ [false,true],
    p ++ [true,false], p ++ [true,true]}

private theorem local_reply_table (q : Address) :
    (readout q defectB = readout q defectD ↔ q ∉ support []) ∧
    (ActualCoarseReadoutHistory.kappa (readout q defectB) =
      ActualCoarseReadoutHistory.kappa (readout q defectD) ↔ q ∉ support []) := by
  cases q with
  | nil => simp [support, readout, defectB, defectD]
  | cons b q =>
    cases q with
    | nil => cases b <;> decide
    | cons c q =>
      cases q with
      | nil => cases b <;> cases c <;> decide
      | cons d q =>
        cases b <;> cases c <;> cases d <;>
          simp [support, readout, defectB, defectD]

private theorem fill_readout_congr (t : Source) (a b : Address → Bool) (q : Address)
    (same : ∀ p ∈ positions t, a p ≠ b p → q ∉ support p) :
    readout q (fill t a) = readout q (fill t b) := by
  induction t generalizing a b q with
  | of c => rfl
  | mul l r ihl ihr =>
    by_cases ht : .mul l r = defectB
    · have eq_or_out : a [] = b [] ∨ q ∉ support [] := by
        by_cases hab : a [] = b []
        · exact Or.inl hab
        · exact Or.inr (same [] (by rw [ht]; decide) hab)
      rw [fill, fill, if_pos ht, if_pos ht]
      rcases eq_or_out with eq | out
      · rw [eq]
      · have he := (local_reply_table q).1.mpr out
        cases a [] <;> cases b [] <;> simp_all
    · rw [fill, fill, if_neg ht, if_neg ht]
      cases q with
      | nil => rfl
      | cons c q =>
        cases c with
        | false =>
          apply ihl
          intro p hp hab
          have mem : false :: p ∈ positions (.mul l r) := by simp [positions, hp]
          simpa [support, List.cons_append] using same (false :: p) mem hab
        | true =>
          apply ihr
          intro p hp hab
          have mem : true :: p ∈ positions (.mul l r) := by simp [positions, hp]
          simpa [support, List.cons_append] using same (true :: p) mem hab

/-- Arbitrarily deep queries outside all changed six-address supports have equal replies. -/
theorem outside_support_invariance (t : Source) (A B : Finset Address)
    (_hA : A ⊆ positions t) (_hB : B ⊆ positions t) (q : Address)
    (outside : ∀ p ∈ A ∆ B, q ∉ support p) :
    readout q (variant t A) = readout q (variant t B) := by
  apply fill_readout_congr
  intro p _ different
  apply outside p
  by_cases ha : p ∈ A <;> by_cases hb : p ∈ B <;>
    simp_all [Finset.mem_symmDiff]

private theorem reply_at (t : Source) (a : Address → Bool) (p z : Address)
    (hp : p ∈ positions t) :
    readout (p ++ z) (fill t a) = readout z (if a p then defectD else defectB) := by
  have h := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    p z (fill t a)
  rw [fill_at t a p hp] at h
  exact h

private theorem hit_determines_bit (t : Source) (A B : Finset Address)
    (p q : Address) (hp : p ∈ positions t) (hq : q ∈ support p)
    (same : readout q (variant t A) = readout q (variant t B)) :
    (p ∈ A ↔ p ∈ B) := by
  have at_suffix (z : Address) (hz : z ∈ support []) :
      readout (p ++ z) (variant t A) = readout (p ++ z) (variant t B) →
      (p ∈ A ↔ p ∈ B) := by
    unfold variant
    rw [reply_at t _ p z hp, reply_at t _ p z hp]
    have ne := mt (local_reply_table z).1.mp (not_not.mpr hz)
    have ne' := Ne.symm ne
    by_cases ha : p ∈ A <;> by_cases hb : p ∈ B <;> simp_all
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact at_suffix _ (by simp [support]) same

/-- The original positions whose supports occur in a chronological raw history. -/
def hit (t : Source) (h : Hist (fun _ : Address => Reply)) : Finset Address :=
  (positions t).filter (fun p => ∃ e ∈ h, e.1 ∈ support p)

/-- Exact agreement with every recorded reply, including repetitions and absent replies. -/
def Consistent (t : Source) (A : Finset Address) (h : Hist (fun _ : Address => Reply)) : Prop :=
  ∀ e ∈ h, readout e.1 (variant t A) = e.2

/-- A truthful record fixes exactly the hit bits, with no restrictions on the other bits. -/
private theorem record_face_iff (t : Source) (A B : Finset Address)
    (hA : A ⊆ positions t) (hB : B ⊆ positions t)
    (h : Hist (fun _ : Address => Reply)) (truth : Consistent t A h) :
    Consistent t B h ↔ B ∩ hit t h = A ∩ hit t h := by
  constructor
  · intro consistent
    ext p
    by_cases hp : p ∈ hit t h
    · obtain ⟨pos,e,he,hq⟩ := Finset.mem_filter.mp hp
      have eq := hit_determines_bit t A B p e.1 pos hq
        ((truth e he).trans (consistent e he).symm)
      simp only [Finset.mem_inter, hp, and_true]
      exact eq.symm
    · simp [hp]
  · intro eq e he
    have same : readout e.1 (variant t B) = readout e.1 (variant t A) := by
      apply outside_support_invariance t B A hB hA
      intro p hp hq
      have pos : p ∈ positions t := by
        rcases Finset.mem_symmDiff.mp hp with ⟨hb,_⟩ | ⟨ha,_⟩
        · exact hB hb
        · exact hA ha
      have hh : p ∈ hit t h := Finset.mem_filter.mpr ⟨pos,e,he,hq⟩
      have mem := Finset.ext_iff.mp eq p
      simp only [Finset.mem_inter, hh, and_true] at mem
      rcases Finset.mem_symmDiff.mp hp with ⟨hb,ha⟩ | ⟨ha,hb⟩
      · exact ha (mem.mp hb)
      · exact hb (mem.mpr ha)
    exact same.trans (truth e he)

/-- Every subset of original positions consistent with the raw record. -/
def compatible (t : Source) (h : Hist (fun _ : Address => Reply)) : Finset (Finset Address) :=
  (positions t).powerset.filter (fun A => Consistent t A h)

/-- The actual native sources, retaining all original brackets and labels. -/
def compatibleSources (t : Source) (h : Hist (fun _ : Address => Reply)) : Finset Source :=
  (compatible t h).image (variant t)

/-- Conditioning the uniform law on all subsets on the observed nonempty fiber. -/
def posterior (t : Source) (h : Hist (fun _ : Address => Reply)) : compatible t h → ℝ :=
  fun _ => (2 ^ (positions t).card : ℝ)⁻¹ /
    ∑ _ : compatible t h, (2 ^ (positions t).card : ℝ)⁻¹

private theorem face_card (t : Source) (A : Finset Address) (hA : A ⊆ positions t)
    (h : Hist (fun _ : Address => Reply)) (truth : Consistent t A h) :
    (compatible t h).card = 2 ^ ((positions t).card - (hit t h).card) := by
  let H := hit t h
  have hH : H ⊆ positions t := Finset.filter_subset _ _
  have eq : compatible t h = Finset.Icc (A ∩ H) ((A ∩ H) ∪ (positions t \ H)) := by
    ext B
    simp only [compatible, Finset.mem_filter, Finset.mem_powerset, Finset.mem_Icc]
    constructor
    · rintro ⟨hB,consistent⟩
      have same := (record_face_iff t A B hA hB h truth).mp consistent
      constructor
      · intro p hp
        have mem : p ∈ B ∩ H := by rw [same]; exact hp
        exact (Finset.mem_inter.mp mem).1
      · intro p hp
        by_cases hh : p ∈ H
        · apply Finset.mem_union_left
          rw [← same]
          exact Finset.mem_inter.mpr ⟨hp,hh⟩
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hB hp,hh⟩)
    · rintro ⟨lower,upper⟩
      have hB : B ⊆ positions t := by
        intro p hp
        rcases Finset.mem_union.mp (upper hp) with mem | mem
        · exact hA (Finset.mem_inter.mp mem).1
        · exact (Finset.mem_sdiff.mp mem).1
      refine ⟨hB,(record_face_iff t A B hA hB h truth).mpr ?_⟩
      ext p
      constructor
      · rintro mem
        obtain ⟨hb,hh⟩ := Finset.mem_inter.mp mem
        rcases Finset.mem_union.mp (upper hb) with ha | ha
        · exact ha
        · exact False.elim ((Finset.mem_sdiff.mp ha).2 hh)
      · intro hp
        exact Finset.mem_inter.mpr ⟨lower hp,(Finset.mem_inter.mp hp).2⟩
  have disj : Disjoint (A ∩ H) (positions t \ H) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [eq, Finset.card_Icc_finset Finset.subset_union_left,
    Finset.card_union_of_disjoint disj, Finset.card_sdiff_of_subset hH]
  simp [H]

/-- The observation face has its exact cardinality and the uniform conditional law,
whose Shannon entropy in bits is the number of unhit positions. -/
theorem native_record_face (n : ℕ) (hn : 3 ≤ n) (A : Finset Address)
    (hA : A ⊆ positions (T n)) (h : Hist (fun _ : Address => Reply))
    (truth : Consistent (T n) A h) :
    (∀ B ⊆ positions (T n), Consistent (T n) B h ↔
      B ∩ hit (T n) h = A ∩ hit (T n) h) ∧
    (compatible (T n) h).card = 2 ^ (Nat.fib (n-2) - (hit (T n) h).card) ∧
    (compatibleSources (T n) h).card = 2 ^ (Nat.fib (n-2) - (hit (T n) h).card) ∧
    posterior (T n) h = (fun _ => ((compatible (T n) h).card : ℝ)⁻¹) ∧
    D5.S3.Entropy.MaxEntropy.shannonEntropy (posterior (T n) h) / Real.log 2 =
      (Nat.fib (n-2) - (hit (T n) h).card : ℕ) := by
  have card := face_card (T n) A hA h truth
  rw [(Geometry.NativeAncestryDefectCube.native_area_cube n hn).1] at card
  have mem : A ∈ compatible (T n) h := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hA,truth⟩
  letI : Nonempty (compatible (T n) h) := ⟨⟨A,mem⟩⟩
  have pos : (0 : ℝ) < (compatible (T n) h).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨A,mem⟩
  have powpos : (0 : ℝ) < 2 ^ (positions (T n)).card := by positivity
  have uniform : posterior (T n) h =
      (fun _ => ((compatible (T n) h).card : ℝ)⁻¹) := by
    funext B
    simp only [posterior, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    field_simp [ne_of_gt pos,ne_of_gt powpos]
  have sourcecard : (compatibleSources (T n) h).card = (compatible (T n) h).card := by
    apply Finset.card_image_of_injOn
    intro B hB C hC eq
    have hB' := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have hC' := Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1
    exact congrArg Subtype.val
      ((Geometry.NativeAncestryDefectCube.native_area_cube n hn).2.1
        (a₁ := ⟨B,hB'⟩) (a₂ := ⟨C,hC'⟩) eq)
  refine ⟨fun B hB => record_face_iff (T n) A B hA hB h truth,card,sourcecard.trans card,uniform,?_⟩
  have norm : (∀ B, 0 ≤ posterior (T n) h B) ∧ ∑ B, posterior (T n) h B = 1 := by
    rw [uniform]
    constructor
    · intro B; positivity
    · simp [ne_of_gt pos]
  have entropy := (D5.S3.Entropy.EntropyEquality.entropy_eq_log_card_iff_uniform
    (posterior (T n) h) norm).mpr (by simpa using uniform)
  rw [entropy, Fintype.card_coe, card, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow, mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]

/-- One source-independent history policy, with an actual finite terminal run on every cube input. -/
structure CubeRun (t : Source) where
  policy : Hist (fun _ : Address => Reply) → Sum Address Bool
  trace : Finset Address → Hist (fun _ : Address => Reply)
  answer : Finset Address → Bool
  terminates : ∀ A ⊆ positions t, ∃ fuel,
    execute readout policy fuel [] (variant t A) = some (trace A,answer A)

/-- True means that the original source has no changed position. -/
def Correct (t : Source) (R : CubeRun t) : Prop :=
  ∀ A ⊆ positions t, R.answer A = true ↔ A = ∅

private theorem execute_unique (policy : Hist (fun _ : Address => Reply) → Sum Address Bool)
    (U : Source) (m n : ℕ) (x y : Hist (fun _ : Address => Reply) × Bool)
    (hx : execute readout policy m [] U = some x)
    (hy : execute readout policy n [] U = some y) : x = y := by
  have ex := D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute_mono
    readout policy m (max m n) [] U x.1 x.2 (le_max_left _ _) hx
  have ey := D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute_mono
    readout policy n (max m n) [] U y.1 y.2 (le_max_right _ _) hy
  exact Option.some.inj (ex.symm.trans ey)

private theorem unhit_singleton (t : Source) (R : CubeRun t) (p : Address)
    (hp : p ∈ positions t) (unhit : p ∉ hit t (R.trace ∅)) :
    R.trace {p} = R.trace ∅ ∧ R.answer {p} = R.answer ∅ := by
  obtain ⟨fuel,run⟩ := R.terminates ∅ (Finset.empty_subset _)
  have replay := execute_transfer readout R.policy fuel [] (variant t ∅)
    (R.trace ∅) (R.answer ∅) run
  have consistent : Consistent t {p} (R.trace ∅) :=
    (record_face_iff t ∅ {p} (Finset.empty_subset _) (by simpa) _ replay.1).mpr
      (by simp [unhit])
  have transferred := replay.2 (variant t {p}) consistent
  obtain ⟨fuel',run'⟩ := R.terminates {p} (by simpa)
  have eq := execute_unique R.policy (variant t {p}) fuel' fuel
    (R.trace {p},R.answer {p}) (R.trace ∅,R.answer ∅) run' transferred
  exact Prod.mk.inj eq

private theorem support_prefix (p q : Address) (hq : q ∈ support p) : p.IsPrefix q := by
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_,rfl⟩

private theorem supports_disjoint (n : ℕ) (hn : 3 ≤ n) (p r : Address)
    (hp : p ∈ positions (T n)) (hr : r ∈ positions (T n)) (ne : p ≠ r) :
    Disjoint (support p) (support r) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  have prefixes := List.prefix_or_prefix_of_prefix (support_prefix p q hq)
    (support_prefix r q hq')
  have positions_subtree := (Geometry.NativeAncestryDefectCube.native_area_cube n hn).2.2.2.1
  have geometry := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.1
    (T n) p r defectB defectB (Or.inl rfl) (Or.inl rfl)
    ((positions_subtree p).mp hp) ((positions_subtree r).mp hr)
  rcases geometry with eq | inc | bad | bad
  · exact ne eq.1
  · exact prefixes.elim inc.1 inc.2
  · exact (show defectB ≠ ActualImageSevenLeafSeparation.C by decide) bad.1
  · exact (show defectB ≠ ActualImageSevenLeafSeparation.C by decide) bad.2.1

private theorem hit_card_le_paid (n : ℕ) (hn : 3 ≤ n)
    (h : Hist (fun _ : Address => Reply)) : (hit (T n) h).card ≤ (paid h).card := by
  have exists_query (p : hit (T n) h) : ∃ q ∈ paid h, q ∈ support p.val := by
    obtain ⟨_,e,he,hq⟩ := Finset.mem_filter.mp p.property
    exact ⟨e.1,by simp only [paid,List.mem_toFinset,List.mem_map]; exact ⟨e,he,rfl⟩,hq⟩
  let f : hit (T n) h → paid h := fun p =>
    ⟨(exists_query p).choose,(exists_query p).choose_spec.1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro p r eq
  apply Subtype.ext
  by_contra ne
  have disj := supports_disjoint n hn p r
    (Finset.mem_filter.mp p.property).1 (Finset.mem_filter.mp r.property).1 ne
  have pe : (f p).val ∈ support p.val := (exists_query p).choose_spec.2
  have re : (f r).val ∈ support r.val := (exists_query r).choose_spec.2
  exact Finset.disjoint_left.mp disj pe (by simpa only [eq] using re)

private theorem canonical_lower (n : ℕ) (hn : 3 ≤ n) (R : CubeRun (T n))
    (correct : Correct (T n) R) : Nat.fib (n-2) ≤ (paid (R.trace ∅)).card := by
  have allhit : hit (T n) (R.trace ∅) = positions (T n) := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro p hp
    by_contra unhit
    have eq := (unhit_singleton (T n) R p hp unhit).2
    have canonical := (correct ∅ (Finset.empty_subset _)).mpr rfl
    have defect := (correct {p} (by simpa)).mp (eq.trans canonical)
    exact Finset.singleton_ne_empty p defect
  have lower := hit_card_le_paid n hn (R.trace ∅)
  rw [allhit,(Geometry.NativeAncestryDefectCube.native_area_cube n hn).1] at lower
  exact lower

private def scanTree : List Address → PassiveProtocol Address (fun _ => Reply)
  | [] => .stop
  | p :: ps => .query (p ++ [false]) (fun _ => scanTree ps)

private def scanDecode (h : Hist (fun _ : Address => Reply)) : Bool :=
  decide (∀ e ∈ h, ActualCoarseReadoutHistory.kappa e.2 = none)

private theorem scan_transcript (ps : List Address) (U : Source) :
    runPassiveProtocol readout (scanTree ps) U =
      ps.map (fun p => ⟨p ++ [false],readout (p ++ [false]) U⟩) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [scanTree,runPassiveProtocol,List.map_cons,ih]

private def scanRun (t : Source) (J : Finset Address) : CubeRun t where
  policy := D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.treePolicy
    (scanTree J.toList) scanDecode
  trace A := runPassiveProtocol readout (scanTree J.toList) (variant t A)
  answer A := scanDecode (runPassiveProtocol readout (scanTree J.toList) (variant t A))
  terminates A _ := ⟨_,
    D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.tree_execution
      readout (scanTree J.toList) scanDecode (variant t A)⟩

private theorem scan_answer (t : Source) (J A : Finset Address) (hJ : J ⊆ positions t) :
    (scanRun t J).answer A = true ↔ A ∩ J = ∅ := by
  have at_left (p : Address) (hp : p ∈ J) :
      ActualCoarseReadoutHistory.kappa (readout (p ++ [false]) (variant t A)) = none ↔ p ∉ A := by
    unfold variant
    rw [reply_at t _ p [false] (hJ hp)]
    by_cases ha : p ∈ A <;> simp [ha,defectB,defectD,readout,ActualCoarseReadoutHistory.kappa]
  change scanDecode (runPassiveProtocol readout (scanTree J.toList) (variant t A)) = true ↔ _
  rw [scan_transcript]
  simp only [scanDecode,decide_eq_true_eq,List.forall_mem_map,Finset.mem_toList]
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro all p hp
    obtain ⟨ha,hp⟩ := Finset.mem_inter.mp hp
    exact ((at_left p hp).mp (all p hp)) ha
  · intro empty p hp
    apply (at_left p hp).mpr
    intro ha
    exact empty p (Finset.mem_inter.mpr ⟨ha,hp⟩)

private theorem scan_paid (t : Source) (J A : Finset Address) :
    (paid ((scanRun t J).trace A)).card = J.card := by
  have eq : paid ((scanRun t J).trace A) = J.image (fun p => p ++ [false]) := by
    ext q
    simp only [scanRun,scan_transcript,paid,List.mem_toFinset,List.mem_map,Finset.mem_toList,
      Finset.mem_image]
    constructor
    · rintro ⟨e,⟨p,hp,rfl⟩,rfl⟩; exact ⟨p,hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩; exact ⟨_,⟨p,hp,rfl⟩,rfl⟩
  rw [eq,Finset.card_image_of_injective]
  intro p r eq
  exact List.append_cancel_right eq

private theorem scan_hit (n : ℕ) (hn : 3 ≤ n) (J A : Finset Address)
    (hJ : J ⊆ positions (T n)) : hit (T n) ((scanRun (T n) J).trace A) = J := by
  ext p
  simp only [hit,Finset.mem_filter]
  constructor
  · rintro ⟨hp,e,he,hq⟩
    change e ∈ runPassiveProtocol readout (scanTree J.toList) (variant (T n) A) at he
    rw [scan_transcript] at he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    have rmem : r ∈ J := by simpa using hr
    by_cases eq : r = p
    · exact eq ▸ rmem
    · have disj := supports_disjoint n hn r p (hJ rmem) hp eq
      exact False.elim (Finset.disjoint_left.mp disj (by simp [support]) hq)
  · intro hp
    refine ⟨hJ hp,⟨p ++ [false],readout (p ++ [false]) (variant (T n) A)⟩,?_,by simp [support]⟩
    change _ ∈ runPassiveProtocol readout (scanTree J.toList) (variant (T n) A)
    rw [scan_transcript]
    exact List.mem_map.mpr ⟨p,by simpa using hp,rfl⟩

private theorem scan_coarse (t : Source) (J : Finset Address) :
    Function.FactorsThrough (scanRun t J).policy ActualCoarseReadoutHistory.kappa_hist := by
  let κH := ActualCoarseReadoutHistory.kappa_hist
  have stopped (h : Hist (fun _ : Address => Reply)) :
      D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual
        (.stop : PassiveProtocol Address (fun _ => Reply)) h = .stop := by
    induction h with
    | nil => rfl
    | cons e h ih => exact ih
  have sameResidual (ps : List Address) : ∀ h k, κH h = κH k →
      D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual (scanTree ps) h =
      D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual (scanTree ps) k := by
    induction ps with
    | nil => intro h k _; exact (stopped h).trans (stopped k).symm
    | cons p ps ih =>
      intro h k eq
      cases h with
      | nil =>
        cases k with
        | nil => rfl
        | cons e k => simp [κH,ActualCoarseReadoutHistory.kappa_hist] at eq
      | cons e h =>
        cases k with
        | nil => simp [κH,ActualCoarseReadoutHistory.kappa_hist] at eq
        | cons f k =>
          have heads := List.cons.inj (show
            (⟨e.1,ActualCoarseReadoutHistory.kappa e.2⟩ : Sigma (fun _ : Address => Option Bool)) :: κH h =
            ⟨f.1,ActualCoarseReadoutHistory.kappa f.2⟩ :: κH k from eq)
          have addr := congrArg Sigma.fst heads.1
          change D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual
            (D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.advance (scanTree (p::ps)) e) h =
            D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual
            (D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.advance (scanTree (p::ps)) f) k
          by_cases hit : e.1 = p ++ [false]
          · have fhit : f.1 = p ++ [false] := addr.symm.trans hit
            simpa [scanTree,D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.advance,
              hit,fhit] using ih h k heads.2
          · have fhit : f.1 ≠ p ++ [false] := fun ff => hit (addr.trans ff)
            simp only [scanTree,D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.advance,
              hit,fhit,↓reduceDIte]
            exact (stopped h).trans (stopped k).symm
  intro h k eq
  have decoder (h : Hist (fun _ : Address => Reply)) : scanDecode h =
      decide (∀ e ∈ κH h, e.2 = none) := by
    have condition : (∀ e ∈ h, ActualCoarseReadoutHistory.kappa e.2 = none) ↔
        (∀ e ∈ κH h, e.2 = none) := by
      constructor
      · intro all e he
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
        exact all a ha
      · intro all e he
        exact all ⟨e.1,ActualCoarseReadoutHistory.kappa e.2⟩
          (List.mem_map.mpr ⟨e,he,rfl⟩)
    simp only [scanDecode,condition]
  change D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.treePolicy
    (scanTree J.toList) scanDecode h =
    D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.treePolicy
      (scanTree J.toList) scanDecode k
  unfold D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.treePolicy
  rw [sameResidual J.toList h k eq]
  cases D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.residual (scanTree J.toList) k with
  | stop =>
    change (Sum.inr (scanDecode h) : Sum Address Bool) = .inr (scanDecode k)
    rw [decoder h,decoder k]
    change κH h = κH k at eq
    rw [eq]
  | query a next => rfl

/-- Every correct policy pays at least the number of positions on the canonical input;
a fixed left-child scan attains that value and bounds the cost on every input. -/
theorem optimal_canonical_queries (n : ℕ) (hn : 3 ≤ n) :
    (∀ R : CubeRun (T n), Correct (T n) R →
      Nat.fib (n-2) ≤ (paid (R.trace ∅)).card) ∧
    ∃ R : CubeRun (T n), Correct (T n) R ∧
      Function.FactorsThrough R.policy ActualCoarseReadoutHistory.kappa_hist ∧
      (∀ A ⊆ positions (T n), (paid (R.trace A)).card ≤ Nat.fib (n-2)) ∧
      (paid (R.trace ∅)).card = Nat.fib (n-2) := by
  refine ⟨canonical_lower n hn,scanRun (T n) (positions (T n)),?_,scan_coarse _ _,?_,?_⟩
  · intro A hA
    rw [scan_answer _ _ _ (Finset.Subset.refl _),Finset.inter_eq_left.mpr hA]
  · intro A _
    rw [scan_paid,(Geometry.NativeAncestryDefectCube.native_area_cube n hn).1]
  · rw [scan_paid,(Geometry.NativeAncestryDefectCube.native_area_cube n hn).1]

/-- Half the prior mass is canonical; the other half is uniform over singleton defects. -/
def success (t : Source) (R : CubeRun t) : ℝ :=
  (if R.answer ∅ then 1/2 else 0) +
    (((positions t).filter (fun p => R.answer {p} = false)).card : ℝ) /
      (2 * (positions t).card)

private theorem success_nonneg (t : Source) (R : CubeRun t) : 0 ≤ success t R := by
  unfold success
  positivity

private theorem seedwise_bound (n : ℕ) (hn : 3 ≤ n) (q : ℕ) (R : CubeRun (T n))
    (budget : ∀ A ⊆ positions (T n), (hit (T n) (R.trace A)).card ≤ q) :
    success (T n) R ≤ 1/2 + (q : ℝ) / (2 * Nat.fib (n-2)) := by
  have card := (Geometry.NativeAncestryDefectCube.native_area_cube n hn).1
  have kpos : (0 : ℝ) < Nat.fib (n-2) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < n-2)
  by_cases canonical : R.answer ∅ = true
  · have subset : (positions (T n)).filter (fun p => R.answer {p} = false) ⊆
        hit (T n) (R.trace ∅) := by
      intro p hp
      obtain ⟨pos,neg⟩ := Finset.mem_filter.mp hp
      by_contra no
      have eq := (unhit_singleton (T n) R p pos no).2
      rw [canonical,neg] at eq
      cases eq
    have bound : (((positions (T n)).filter (fun p => R.answer {p} = false)).card : ℝ) ≤ q := by
      exact_mod_cast (Finset.card_le_card subset).trans (budget ∅ (Finset.empty_subset _))
    simp only [success,canonical,ite_true,card]
    exact add_le_add le_rfl (div_le_div_of_nonneg_right bound
      (by positivity : (0:ℝ) ≤ 2 * Nat.fib (n-2)))
  · have bound : (((positions (T n)).filter (fun p => R.answer {p} = false)).card : ℝ) ≤
        Nat.fib (n-2) := by
      exact_mod_cast (Finset.card_filter_le _ _).trans card.le
    have canonical_false : R.answer ∅ = false := Bool.eq_false_of_not_eq_true canonical
    simp only [success,canonical_false,Bool.false_eq_true,↓reduceIte,zero_add,card]
    have half : (((positions (T n)).filter (fun p => R.answer {p} = false)).card : ℝ) /
        (2*Nat.fib (n-2)) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<2*Nat.fib (n-2))).mpr
      linarith
    exact half.trans (le_add_of_nonneg_right
      (by positivity : (0:ℝ) ≤ (q:ℝ) / (2 * Nat.fib (n-2))))

private theorem scan_success (n : ℕ) (hn : 3 ≤ n) (J : Finset Address)
    (hJ : J ⊆ positions (T n)) :
    success (T n) (scanRun (T n) J) = 1/2 + (J.card : ℝ)/(2*Nat.fib (n-2)) := by
  have canonical : (scanRun (T n) J).answer ∅ = true :=
    (scan_answer _ _ _ hJ).mpr (by simp)
  have defects : (positions (T n)).filter (fun p => (scanRun (T n) J).answer {p} = false) = J := by
    ext p
    have ans := scan_answer (T n) J {p} hJ
    by_cases hp : p ∈ J
    · have neg : (scanRun (T n) J).answer {p} = false := by
        cases he : (scanRun (T n) J).answer {p} with
        | false => rfl
        | true => have no := ans.mp he; simpa [hp] using no
      simp [hp,hJ hp,neg]
    · have pos : (scanRun (T n) J).answer {p} = true := ans.mpr (by simp [hp])
      simp [hp,pos]
  simp only [success,canonical,ite_true,defects,
    (Geometry.NativeAncestryDefectCube.native_area_cube n hn).1]

/-- The indicator of a correct terminal classification on one fixed input. -/
def reward {t : Source} (R : CubeRun t) (A : Finset Address) : ℝ :=
  if R.answer A = decide (A = ∅) then 1 else 0

private theorem success_reward_sum (t : Source) (R : CubeRun t) :
    success t R = (1/2:ℝ) * reward R ∅ +
      (∑ p ∈ positions t, reward R {p}) / (2*(positions t).card) := by
  have sum : (∑ p ∈ positions t, reward R {p}) =
      (((positions t).filter (fun p => R.answer {p} = false)).card : ℝ) := by
    simpa only [reward,Finset.singleton_ne_empty,decide_false] using
      (Finset.sum_boole (fun p => R.answer {p} = false) (positions t) :
        (∑ p ∈ positions t, if R.answer {p} = false then (1:ℝ) else 0) = _)
  rw [sum]
  cases he : R.answer ∅ <;> simp [success,reward,he]

private theorem averaged_bound (n : ℕ) (hn : 3 ≤ n) (q : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (R : Ω → CubeRun (T n))
    (budget : ∀ ω A, A ⊆ positions (T n) → (hit (T n) ((R ω).trace A)).card ≤ q) :
    ∫ ω, success (T n) (R ω) ∂μ ≤ 1/2 + (q : ℝ)/(2*Nat.fib (n-2)) := by
  have bound := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_of_all μ (fun ω => success_nonneg (T n) (R ω)))
    (MeasureTheory.integrable_const (1/2+(q:ℝ)/(2*Nat.fib (n-2))))
    (MeasureTheory.ae_of_all μ (fun ω => seedwise_bound n hn q (R ω) (budget ω)))
  simpa only [MeasureTheory.integral_const,MeasureTheory.probReal_univ,one_smul] using bound

private theorem uniform_error_lower (n : ℕ) (hn : 3 ≤ n) (q : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (R : Ω → CubeRun (T n)) (δ : ℝ) (hδ : δ < 1/2)
    (budget : ∀ ω A, A ⊆ positions (T n) → (hit (T n) ((R ω).trace A)).card ≤ q)
    (accurate : ∀ A ⊆ positions (T n), 1-δ ≤ ∫ ω, reward (R ω) A ∂μ) :
    (1-2*δ)*(Nat.fib (n-2) : ℝ) ≤ q := by
  have integrable (A : Finset Address) (hA : A ⊆ positions (T n)) :
      MeasureTheory.Integrable (fun ω => reward (R ω) A) μ := by
    apply MeasureTheory.Integrable.of_integral_ne_zero
    have pos : (0:ℝ) < ∫ ω, reward (R ω) A ∂μ := lt_of_lt_of_le (by linarith) (accurate A hA)
    exact ne_of_gt pos
  have sumint : MeasureTheory.Integrable (fun ω => ∑ p ∈ positions (T n), reward (R ω) {p}) μ :=
    MeasureTheory.integrable_finsetSum _ (fun p hp => integrable {p} (by simpa))
  have expression : (∫ ω, success (T n) (R ω) ∂μ) =
      (1/2:ℝ) * (∫ ω, reward (R ω) ∅ ∂μ) +
        (∑ p ∈ positions (T n), ∫ ω, reward (R ω) {p} ∂μ) /
          (2*(positions (T n)).card) := by
    simp_rw [success_reward_sum]
    rw [MeasureTheory.integral_add
      ((integrable ∅ (Finset.empty_subset _)).const_mul _) (sumint.div_const _),
      MeasureTheory.integral_const_mul,MeasureTheory.integral_div,
      MeasureTheory.integral_finsetSum]
    intro p hp
    exact integrable {p} (by simpa)
  have sum_lower : ((positions (T n)).card : ℝ)*(1-δ) ≤
      ∑ p ∈ positions (T n), ∫ ω, reward (R ω) {p} ∂μ := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      Finset.sum_le_sum (fun p hp => accurate {p} (by simpa))
  have card := (Geometry.NativeAncestryDefectCube.native_area_cube n hn).1
  have kpos : (0:ℝ) < Nat.fib (n-2) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0<n-2)
  have canonical := accurate ∅ (Finset.empty_subset _)
  have upper := averaged_bound n hn q μ R budget
  rw [expression,card] at upper
  rw [card] at sum_lower
  have divlower : (1-δ)/2 ≤
      (∑ p ∈ positions (T n), ∫ ω, reward (R ω) {p} ∂μ)/(2*Nat.fib (n-2)) := by
    calc
      (1-δ)/2 = ((Nat.fib (n-2) : ℝ)*(1-δ))/(2*Nat.fib (n-2)) := by
        field_simp [ne_of_gt kpos]
      _ ≤ _ := div_le_div_of_nonneg_right sum_lower (by positivity)
  have fraclower : (1/2:ℝ)-δ ≤ (q:ℝ)/(2*Nat.fib (n-2)) := by linarith
  have mul_upper := (le_div_iff₀ (by positivity : (0:ℝ)<2*Nat.fib (n-2))).mp fraclower
  nlinarith

/-- The hard per-input support budget has exact optimal average success.
The same upper bound holds after averaging any source-independent seed law. -/
theorem optimal_single_defect_success (n : ℕ) (hn : 3 ≤ n) (q : ℕ)
    (hq : q ≤ Nat.fib (n-2)) :
    (∀ R : CubeRun (T n),
      (∀ A ⊆ positions (T n), (hit (T n) (R.trace A)).card ≤ q) →
      success (T n) R ≤ 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) ∧
    (∃ R : CubeRun (T n),
      (∀ A ⊆ positions (T n), (hit (T n) (R.trace A)).card ≤ q) ∧
      success (T n) R = 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (R : Ω → CubeRun (T n)),
      Measurable (fun ω => success (T n) (R ω)) →
      (∀ ω A, A ⊆ positions (T n) → (hit (T n) ((R ω).trace A)).card ≤ q) →
      ∫ ω, success (T n) (R ω) ∂μ ≤ 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (R : Ω → CubeRun (T n)) (δ : ℝ), δ < 1/2 →
      (∀ A ⊆ positions (T n), Measurable (fun ω => (R ω).answer A)) →
      (∀ ω A, A ⊆ positions (T n) → (hit (T n) ((R ω).trace A)).card ≤ q) →
      (∀ A ⊆ positions (T n), 1-δ ≤ ∫ ω, reward (R ω) A ∂μ) →
      (1-2*δ)*(Nat.fib (n-2) : ℝ) ≤ q) := by
  refine ⟨seedwise_bound n hn q,?_,?_,?_⟩
  · have hq' : q ≤ (positions (T n)).card := by
      rwa [(Geometry.NativeAncestryDefectCube.native_area_cube n hn).1]
    obtain ⟨J,hJ,card⟩ := Finset.exists_subset_card_eq hq'
    refine ⟨scanRun (T n) J,?_,?_⟩
    · intro A _; rw [scan_hit n hn J A hJ,card]
    · rw [scan_success n hn J hJ,card]
  · intro Ω _ μ _ R _ budget
    exact averaged_bound n hn q μ R budget
  · intro Ω _ μ _ R δ hδ _ budget accurate
    exact uniform_error_lower n hn q μ R δ hδ budget accurate

end
#print axioms outside_support_invariance
#print axioms native_record_face
#print axioms optimal_canonical_queries
#print axioms optimal_single_defect_success
end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
