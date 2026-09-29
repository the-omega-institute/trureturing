/- GID: D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite additive readouts give block matrices and flat reduced spectra. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Sharpness.FreeNegentropyBudget
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/- This remains a same-target partial implementation of theorem 104.1.
The actual joint state and reduced entropy identities are proved here;
explicit eigenspaces, singular values, and the full application remain open. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum

open scoped BigOperators Matrix ComplexOrder MatrixOrder CStarAlgebra
open scoped Classical
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

variable {G A B : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
  [Fintype G] [Fintype A] [Fintype B]
  [DecidableEq G] [DecidableEq A] [DecidableEq B]

def kernelSum (alpha : G →+ A) (beta : G →+ B) : AddSubgroup G :=
  alpha.ker ⊔ beta.ker

abbrev BlockQuotient (alpha : G →+ A) (beta : G →+ B) :=
  G ⧸ kernelSum alpha beta

noncomputable instance blockQuotientFintype (alpha : G →+ A) (beta : G →+ B) :
    Fintype (BlockQuotient alpha beta) := Fintype.ofFinite _

def leftBlock (alpha : G →+ A) (beta : G →+ B)
    (q : BlockQuotient alpha beta) (a : A) : Prop :=
  ∃ x : G, (QuotientAddGroup.mk' (kernelSum alpha beta)) x = q ∧ alpha x = a

def rightBlock (alpha : G →+ A) (beta : G →+ B)
    (q : BlockQuotient alpha beta) (b : B) : Prop :=
  ∃ x : G, (QuotientAddGroup.mk' (kernelSum alpha beta)) x = q ∧ beta x = b

noncomputable def actualCoefficient (alpha : G →+ A) (beta : G →+ B) :
    Matrix A B ℂ :=
  fun a b => (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ *
    ∑ x : G, if alpha x = a ∧ beta x = b then (1 : ℂ) else 0

noncomputable def actualJoint (alpha : G →+ A) (beta : G →+ B) :
    Matrix (A × B) (A × B) ℂ :=
  fun p r => actualCoefficient alpha beta p.1 p.2 *
    star (actualCoefficient alpha beta r.1 r.2)

noncomputable def actualReducedA (alpha : G →+ A) (beta : G →+ B) :
    Matrix A A ℂ := partialTraceRight (actualJoint alpha beta)

noncomputable def actualReducedB (alpha : G →+ A) (beta : G →+ B) :
    Matrix B B ℂ := partialTraceLeft (actualJoint alpha beta)

noncomputable def leftVectors (alpha : G →+ A) (beta : G →+ B) :
    Matrix A (BlockQuotient alpha beta) ℂ :=
  fun a q => (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ)⁻¹ *
    if leftBlock alpha beta q a then 1 else 0

noncomputable def rightVectors (alpha : G →+ A) (beta : G →+ B) :
    Matrix B (BlockQuotient alpha beta) ℂ :=
  fun b q => (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ)⁻¹ *
    if rightBlock alpha beta q b then 1 else 0

noncomputable def blockWeight (alpha : G →+ A) (beta : G →+ B) : ℝ :=
  (Fintype.card alpha.ker : ℝ) * Fintype.card beta.ker / Fintype.card G

omit [Fintype G] [Fintype A] [Fintype B]
  [DecidableEq G] [DecidableEq A] [DecidableEq B] in
/-- Two quotient-block labels meet precisely when they arise from one actual source. -/
theorem paired_block_iff (alpha : G →+ A) (beta : G →+ B) (a : A) (b : B) :
    (∃ x : G, alpha x = a ∧ beta x = b) ↔
      ∃ q : BlockQuotient alpha beta,
        leftBlock alpha beta q a ∧ rightBlock alpha beta q b := by
  constructor
  · rintro ⟨x, ha, hb⟩
    refine ⟨(QuotientAddGroup.mk' (kernelSum alpha beta)) x, ?_, ?_⟩
    · exact ⟨x, rfl, ha⟩
    · exact ⟨x, rfl, hb⟩
  · rintro ⟨q, ⟨x, hxq, hxa⟩, ⟨y, hyq, hyb⟩⟩
    have hxy : x - y ∈ kernelSum alpha beta :=
      QuotientAddGroup.eq_iff_sub_mem.mp (hxq.trans hyq.symm)
    obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp hxy
    have has : alpha s = 0 := hs
    have hbt : beta t = 0 := ht
    refine ⟨x - s, ?_, ?_⟩
    · simpa [map_sub, has] using hxa
    · have h : x - s = y + t := by
        apply (sub_eq_iff_eq_add).2
        calc
          x = (x - y) + y := by abel
          _ = (s + t) + y := by rw [← hst]
          _ = (y + t) + s := by abel
      rw [h, map_add, hbt, add_zero]
      exact hyb

/-- The actual source amplitude has exactly one nonzero term in its quotient block. -/
theorem actual_coefficient_block (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) (a : A) (b : B) :
    actualCoefficient alpha beta a b =
      (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ *
        ∑ q : BlockQuotient alpha beta,
          if leftBlock alpha beta q a ∧ rightBlock alpha beta q b then (1 : ℂ) else 0 := by
  classical
  let d : ℂ := (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹
  have hsingleSource :
      (∑ x : G, if alpha x = a ∧ beta x = b then (1 : ℂ) else 0) =
        if ∃ x : G, alpha x = a ∧ beta x = b then 1 else 0 := by
    by_cases h : ∃ x : G, alpha x = a ∧ beta x = b
    · obtain ⟨x, hxa, hxb⟩ := h
      rw [Finset.sum_eq_single x]
      · have hex : ∃ x : G, alpha x = a ∧ beta x = b := ⟨x, hxa, hxb⟩
        simp [hxa, hxb, hex]
      · intro y _ hy
        have hnot : ¬(alpha y = a ∧ beta y = b) := by
          intro hyab
          exact hy (hpair (show (alpha y, beta y) = (alpha x, beta x) by
            simp [hyab.1, hyab.2, hxa, hxb]))
        simp [hnot]
      · simp
    · have hz : ∀ x : G, ¬(alpha x = a ∧ beta x = b) := by
        intro x hx
        exact h ⟨x, hx⟩
      simp [h, hz]
  have hsingleBlock :
      (∑ q : BlockQuotient alpha beta,
        if leftBlock alpha beta q a ∧ rightBlock alpha beta q b then (1 : ℂ) else 0) =
        if ∃ x : G, alpha x = a ∧ beta x = b then 1 else 0 := by
    by_cases h : ∃ x : G, alpha x = a ∧ beta x = b
    · obtain ⟨x, hxa, hxb⟩ := h
      let qx : BlockQuotient alpha beta :=
        (QuotientAddGroup.mk' (kernelSum alpha beta)) x
      rw [Finset.sum_eq_single qx]
      · have hq : leftBlock alpha beta qx a ∧ rightBlock alpha beta qx b :=
          ⟨⟨x, rfl, hxa⟩, ⟨x, rfl, hxb⟩⟩
        have hex : ∃ x : G, alpha x = a ∧ beta x = b := ⟨x, hxa, hxb⟩
        simp [hq, hex]
      · intro q _ hq
        have hnot : ¬(leftBlock alpha beta q a ∧ rightBlock alpha beta q b) := by
          intro hqb
          obtain ⟨y, hyq, hya⟩ := hqb.1
          have hxy : y - x ∈ kernelSum alpha beta := by
            apply AddSubgroup.mem_sup_left
            change alpha (y - x) = 0
            simp [map_sub, hya, hxa]
          have hqy : q = qx := by
            rw [← hyq]
            exact QuotientAddGroup.eq_iff_sub_mem.mpr hxy
          exact hq hqy
        simp [hnot]
      · simp
    · have hz : ∀ q : BlockQuotient alpha beta,
          ¬(leftBlock alpha beta q a ∧ rightBlock alpha beta q b) := by
        intro q hq
        exact h ((paired_block_iff alpha beta a b).mpr ⟨q, hq⟩)
      simp [h, hz]
  simp only [actualCoefficient]
  rw [hsingleSource, hsingleBlock]

/-- Every right block contains exactly one label for each element of the left kernel. -/
theorem right_block_card (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x)))
    (q : BlockQuotient alpha beta) :
    (Finset.univ.filter (rightBlock alpha beta q)).card = Fintype.card alpha.ker := by
  classical
  obtain ⟨x, hxq⟩ := QuotientAddGroup.mk'_surjective (kernelSum alpha beta) q
  let f : alpha.ker → {b : B // rightBlock alpha beta q b} :=
    fun s => ⟨beta (x + s.1), ⟨x + s.1, by
      rw [← hxq]
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have h : (x + s.1) - x = s.1 := by abel
      rw [h]
      exact AddSubgroup.mem_sup_left s.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    have hb : beta (x + s.1) = beta (x + t.1) := congrArg Subtype.val hst
    have hb' : beta s.1 = beta t.1 := by
      have hh : beta x + beta s.1 = beta x + beta t.1 := by
        simpa only [map_add] using hb
      exact add_left_cancel hh
    have ha' : alpha s.1 = alpha t.1 := by
      have hs0 : alpha s.1 = 0 := s.2
      have ht0 : alpha t.1 = 0 := t.2
      rw [hs0, ht0]
    exact hpair (Prod.ext ha' hb')
  have hsurj : Function.Surjective f := by
    rintro ⟨b, ⟨y, hyq, hyb⟩⟩
    have hyx : y - x ∈ kernelSum alpha beta :=
      QuotientAddGroup.eq_iff_sub_mem.mp (hyq.trans hxq.symm)
    obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp hyx
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    change beta (x + s) = b
    have hy : y = x + s + t := by
      calc
        y = x + (y - x) := by abel
        _ = x + (s + t) := by rw [← hst]
        _ = x + s + t := by abel
    rw [← hyb, hy]
    simp [map_add, show beta t = 0 from ht]
  have hc : Fintype.card alpha.ker =
      Fintype.card {b : B // rightBlock alpha beta q b} :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa [Fintype.card_subtype] using hc.symm

/-- Paired injectivity makes the two kernels disjoint and determines the quotient count. -/
theorem kernel_quotient_normalization (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    alpha.ker ⊓ beta.ker = ⊥ ∧
      Nat.card (kernelSum alpha beta) = Nat.card alpha.ker * Nat.card beta.ker ∧
      Nat.card G = Nat.card (BlockQuotient alpha beta) *
        Nat.card alpha.ker * Nat.card beta.ker := by
  classical
  have hdisj : alpha.ker ⊓ beta.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    have ha : alpha z = 0 := hz.1
    have hb : beta z = 0 := hz.2
    have hz0 : z = 0 := hpair (show (alpha z, beta z) = (alpha 0, beta 0) by
      simp [ha, hb])
    simpa [hz0]
  let f : alpha.ker × beta.ker → kernelSum alpha beta :=
    fun st => ⟨st.1.1 + st.2.1, AddSubgroup.mem_sup.mpr
      ⟨st.1.1, st.1.2, st.2.1, st.2.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    have hh : s.1 + t.1 = s'.1 + t'.1 := congrArg Subtype.val h
    have ha : alpha s.1 = alpha s'.1 := by
      have hs0 : alpha s.1 = 0 := s.2
      have hs0' : alpha s'.1 = 0 := s'.2
      rw [hs0, hs0']
    have hb : beta s.1 = beta s'.1 := by
      have ht0 : beta t.1 = 0 := t.2
      have ht0' : beta t'.1 = 0 := t'.2
      have hm := congrArg beta hh
      simpa [map_add, ht0, ht0'] using hm
    have hs : s = s' := Subtype.ext (hpair (Prod.ext ha hb))
    subst s'
    have ht : t = t' := Subtype.ext (add_left_cancel hh)
    exact Prod.ext rfl ht
  have hf_surj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp hz
    refine ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
    exact Subtype.ext hst
  have hcard : Nat.card (kernelSum alpha beta) =
      Nat.card alpha.ker * Nat.card beta.ker := by
    calc
      Nat.card (kernelSum alpha beta) = Nat.card (alpha.ker × beta.ker) :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
      _ = Nat.card alpha.ker * Nat.card beta.ker := Nat.card_prod _ _
  refine ⟨hdisj, hcard, ?_⟩
  calc
    Nat.card G = Nat.card (BlockQuotient alpha beta) *
        Nat.card (kernelSum alpha beta) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (kernelSum alpha beta)
    _ = Nat.card (BlockQuotient alpha beta) *
        Nat.card alpha.ker * Nat.card beta.ker := by rw [hcard, mul_assoc]

/-- Both realized readout images are disjoint unions of their quotient blocks. -/
theorem readout_block_partitions (alpha : G →+ A) (beta : G →+ B) :
    (∀ a q r, leftBlock alpha beta q a → leftBlock alpha beta r a → q = r) ∧
    (∀ b q r, rightBlock alpha beta q b → rightBlock alpha beta r b → q = r) ∧
    (∀ a, (∃ q, leftBlock alpha beta q a) ↔ a ∈ Set.range alpha) ∧
    (∀ b, (∃ q, rightBlock alpha beta q b) ↔ b ∈ Set.range beta) := by
  constructor
  · intro a q r hqa hra
    obtain ⟨x, hxq, hxa⟩ := hqa
    obtain ⟨y, hyr, hya⟩ := hra
    rw [← hxq, ← hyr]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply AddSubgroup.mem_sup_left
    change alpha (x - y) = 0
    simp [map_sub, hxa, hya]
  constructor
  · intro b q r hqb hrb
    obtain ⟨x, hxq, hxb⟩ := hqb
    obtain ⟨y, hyr, hyb⟩ := hrb
    rw [← hxq, ← hyr]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply AddSubgroup.mem_sup_right
    change beta (x - y) = 0
    simp [map_sub, hxb, hyb]
  constructor
  · intro a
    constructor
    · rintro ⟨q, x, hxq, hxa⟩
      exact ⟨x, hxa⟩
    · rintro ⟨x, hxa⟩
      exact ⟨(QuotientAddGroup.mk' (kernelSum alpha beta)) x, x, rfl, hxa⟩
  · intro b
    constructor
    · rintro ⟨q, x, hxq, hxb⟩
      exact ⟨x, hxb⟩
    · rintro ⟨x, hxb⟩
      exact ⟨(QuotientAddGroup.mk' (kernelSum alpha beta)) x, x, rfl, hxb⟩

/-- The actual source coefficients give normalized block columns and both scaled projections. -/
theorem actual_block_matrices (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    (leftVectors alpha beta)ᴴ * leftVectors alpha beta = 1 ∧
    (rightVectors alpha beta)ᴴ * rightVectors alpha beta = 1 ∧
    actualCoefficient alpha beta =
      (Real.sqrt (blockWeight alpha beta) : ℂ) •
        (leftVectors alpha beta * (rightVectors alpha beta)ᴴ) ∧
    actualReducedA alpha beta = (blockWeight alpha beta : ℂ) •
      (leftVectors alpha beta * (leftVectors alpha beta)ᴴ) ∧
    actualReducedB alpha beta = (blockWeight alpha beta : ℂ) •
      (rightVectors alpha beta * (rightVectors alpha beta)ᴴ) := by
  classical
  let U := leftVectors alpha beta
  let V := rightVectors alpha beta
  let Q := BlockQuotient alpha beta
  have hswap : Function.Injective (fun x : G => (beta x, alpha x)) := by
    intro x y h
    exact hpair (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  have hleft : ∀ q : Q,
      (Finset.univ.filter (leftBlock alpha beta q)).card = Fintype.card beta.ker := by
    intro q
    obtain ⟨x, hxq⟩ := QuotientAddGroup.mk'_surjective (kernelSum alpha beta) q
    let f : beta.ker → {b : A // leftBlock alpha beta q b} :=
      fun s => ⟨alpha (x + s.1), ⟨x + s.1, by
        rw [← hxq]
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        have h : (x + s.1) - x = s.1 := by abel
        rw [h]
        exact AddSubgroup.mem_sup_right s.2, rfl⟩⟩
    have hinj : Function.Injective f := by
      intro s t hst
      apply Subtype.ext
      have hb : alpha (x + s.1) = alpha (x + t.1) := congrArg Subtype.val hst
      have hb' : alpha s.1 = alpha t.1 := by
        have hh : alpha x + alpha s.1 = alpha x + alpha t.1 := by
          simpa only [map_add] using hb
        exact add_left_cancel hh
      have ha' : beta s.1 = beta t.1 := by
        have hs0 : beta s.1 = 0 := s.2
        have ht0 : beta t.1 = 0 := t.2
        rw [hs0, ht0]
      exact hswap (Prod.ext ha' hb')
    have hsurj : Function.Surjective f := by
      rintro ⟨b, ⟨y, hyq, hyb⟩⟩
      have hyx : y - x ∈ kernelSum alpha beta :=
        QuotientAddGroup.eq_iff_sub_mem.mp (hyq.trans hxq.symm)
      obtain ⟨t, ht, s, hs, hts⟩ := AddSubgroup.mem_sup.mp hyx
      have hst : s + t = y - x := (add_comm s t).trans hts
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      change alpha (x + s) = b
      have hy : y = x + s + t := by
        calc
          y = x + (y - x) := by abel
          _ = x + (s + t) := by rw [← hst]
          _ = x + s + t := by abel
      rw [← hyb, hy]
      simp [map_add, show alpha t = 0 from ht]
    have hc : Fintype.card beta.ker =
        Fintype.card {b : A // leftBlock alpha beta q b} :=
      Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    simpa [Fintype.card_subtype] using hc.symm
  have hright (q : Q) :
      (Finset.univ.filter (rightBlock alpha beta q)).card = Fintype.card alpha.ker :=
    right_block_card alpha beta hpair q
  have hpartition := readout_block_partitions alpha beta
  have gramA
      (p : Q → A → Prop) (k : ℕ) (hk : 0 < k)
      (hc : ∀ q, (Finset.univ.filter (p q)).card = k)
      (hd : ∀ i q r, p q i → p r i → q = r) :
      let W : Matrix A Q ℂ := fun i q => (Real.sqrt (k : ℝ) : ℂ)⁻¹ *
        if p q i then 1 else 0
      Wᴴ * W = 1 := by
    let W : Matrix A Q ℂ := fun i q => (Real.sqrt (k : ℝ) : ℂ)⁻¹ *
      if p q i then 1 else 0
    change Wᴴ * W = 1
    ext q r
    change (∑ i : A, star ((Real.sqrt (k : ℝ) : ℂ)⁻¹ *
      if p q i then 1 else 0) * ((Real.sqrt (k : ℝ) : ℂ)⁻¹ *
      if p r i then 1 else 0)) = if q = r then 1 else 0
    have hs : ∑ i : A, (if p q i then (1 : ℂ) else 0) *
        (if p r i then (1 : ℂ) else 0) = if q = r then (k : ℂ) else 0 := by
      by_cases hqr : q = r
      · subst r
        have hi (i : A) : (if p q i then (1 : ℂ) else 0) *
            (if p q i then (1 : ℂ) else 0) = if p q i then 1 else 0 := by
          split_ifs <;> simp
        simp_rw [hi]
        simp only [if_true, Finset.sum_boole, hc]
      · rw [if_neg hqr]
        apply Finset.sum_eq_zero
        intro i _
        by_cases hq : p q i
        · have hr : ¬p r i := fun hr => hqr (hd i q r hq hr)
          simp [hr]
        · simp [hq]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hsqrt : (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = k := by
      norm_cast
      exact Real.mul_self_sqrt (Nat.cast_nonneg k)
    have hsqrt0 : (Real.sqrt (k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hk))
    have hstar (i : A) : star ((Real.sqrt (k : ℝ) : ℂ)⁻¹ *
        if p q i then 1 else 0) =
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ * if p q i then 1 else 0 := by
      split_ifs <;> simp
    simp_rw [hstar]
    have hfactor :
        (∑ i : A, ((Real.sqrt (k : ℝ) : ℂ)⁻¹ * if p q i then 1 else 0) *
          ((Real.sqrt (k : ℝ) : ℂ)⁻¹ * if p r i then 1 else 0)) =
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ * (Real.sqrt (k : ℝ) : ℂ)⁻¹ *
          ∑ i : A, (if p q i then (1 : ℂ) else 0) *
            (if p r i then (1 : ℂ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor, hs]
    by_cases hqr : q = r
    · simp only [hqr, if_true]
      rw [← mul_inv, ← hsqrt]
      exact inv_mul_cancel₀ (mul_ne_zero hsqrt0 hsqrt0)
    · simp [hqr]
  have gramB
      (p : Q → B → Prop) (k : ℕ) (hk : 0 < k)
      (hc : ∀ q, (Finset.univ.filter (p q)).card = k)
      (hd : ∀ i q r, p q i → p r i → q = r) :
      let W : Matrix B Q ℂ := fun i q => (Real.sqrt (k : ℝ) : ℂ)⁻¹ *
        if p q i then 1 else 0
      Wᴴ * W = 1 := by
    let W : Matrix B Q ℂ := fun i q => (Real.sqrt (k : ℝ) : ℂ)⁻¹ *
      if p q i then 1 else 0
    change Wᴴ * W = 1
    ext q r
    change (∑ i : B, star ((Real.sqrt (k : ℝ) : ℂ)⁻¹ *
      if p q i then 1 else 0) * ((Real.sqrt (k : ℝ) : ℂ)⁻¹ *
      if p r i then 1 else 0)) = if q = r then 1 else 0
    have hs : ∑ i : B, (if p q i then (1 : ℂ) else 0) *
        (if p r i then (1 : ℂ) else 0) = if q = r then (k : ℂ) else 0 := by
      by_cases hqr : q = r
      · subst r
        have hi (i : B) : (if p q i then (1 : ℂ) else 0) *
            (if p q i then (1 : ℂ) else 0) = if p q i then 1 else 0 := by
          split_ifs <;> simp
        simp_rw [hi]
        simp only [if_true, Finset.sum_boole, hc]
      · rw [if_neg hqr]
        apply Finset.sum_eq_zero
        intro i _
        by_cases hq : p q i
        · have hr : ¬p r i := fun hr => hqr (hd i q r hq hr)
          simp [hr]
        · simp [hq]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hsqrt : (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = k := by
      norm_cast
      exact Real.mul_self_sqrt (Nat.cast_nonneg k)
    have hsqrt0 : (Real.sqrt (k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hk))
    have hstar (i : B) : star ((Real.sqrt (k : ℝ) : ℂ)⁻¹ *
        if p q i then 1 else 0) =
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ * if p q i then 1 else 0 := by
      split_ifs <;> simp
    simp_rw [hstar]
    have hfactor :
        (∑ i : B, ((Real.sqrt (k : ℝ) : ℂ)⁻¹ * if p q i then 1 else 0) *
          ((Real.sqrt (k : ℝ) : ℂ)⁻¹ * if p r i then 1 else 0)) =
        (Real.sqrt (k : ℝ) : ℂ)⁻¹ * (Real.sqrt (k : ℝ) : ℂ)⁻¹ *
          ∑ i : B, (if p q i then (1 : ℂ) else 0) *
            (if p r i then (1 : ℂ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor, hs]
    by_cases hqr : q = r
    · simp only [hqr, if_true]
      rw [← mul_inv, ← hsqrt]
      exact inv_mul_cancel₀ (mul_ne_zero hsqrt0 hsqrt0)
    · simp [hqr]
  have hU : Uᴴ * U = 1 :=
    gramA (leftBlock alpha beta) (Fintype.card beta.ker)
      Fintype.card_pos hleft hpartition.1
  have hV : Vᴴ * V = 1 :=
    gramB (rightBlock alpha beta) (Fintype.card alpha.ker)
      Fintype.card_pos hright hpartition.2.1
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hKA : (0 : ℝ) < Fintype.card alpha.ker := by exact_mod_cast Fintype.card_pos
  have hKB : (0 : ℝ) < Fintype.card beta.ker := by exact_mod_cast Fintype.card_pos
  have hscale : Real.sqrt (blockWeight alpha beta) =
      Real.sqrt (Fintype.card alpha.ker : ℝ) *
        Real.sqrt (Fintype.card beta.ker : ℝ) /
          Real.sqrt (Fintype.card G : ℝ) := by
    rw [blockWeight, Real.sqrt_div (mul_nonneg hKA.le hKB.le), Real.sqrt_mul hKA.le]
  have hscaleC : (Real.sqrt (blockWeight alpha beta) : ℂ) *
      (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ := by
    rw [hscale]
    push_cast
    have ha : (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr hKA)
    have hb : (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr hKB)
    field_simp [ha, hb]
    <;> ring
  have hC : actualCoefficient alpha beta =
      (Real.sqrt (blockWeight alpha beta) : ℂ) • (U * Vᴴ) := by
    ext a b
    rw [actual_coefficient_block alpha beta hpair]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.conjTranspose_apply, U, V, leftVectors, rightVectors,
      map_mul, map_inv₀, Complex.star_def, Complex.conj_ofReal,
      apply_ite, map_one, map_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases ha : leftBlock alpha beta q a <;>
      by_cases hb : rightBlock alpha beta q b <;>
      simp only [ha, hb, and_self, true_and, false_and, and_false,
        if_true, if_false, mul_one, mul_zero, zero_mul, ← mul_assoc]
    exact hscaleC.symm
  have hreal : (actualCoefficient alpha beta)ᴴ =
      (actualCoefficient alpha beta)ᵀ := by
    ext b a
    simp [actualCoefficient, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hA : actualReducedA alpha beta =
      actualCoefficient alpha beta * (actualCoefficient alpha beta)ᴴ := by
    ext a c
    rfl
  have hB : actualReducedB alpha beta =
      (actualCoefficient alpha beta)ᵀ * actualCoefficient alpha beta := by
    ext b d
    simp only [actualReducedB, partialTraceLeft, actualJoint, Matrix.mul_apply,
      Matrix.transpose_apply]
    have hc (a : A) : star (actualCoefficient alpha beta a d) =
        actualCoefficient alpha beta a d := by simp [actualCoefficient]
    simp_rw [hc]
  have hsq : (Real.sqrt (blockWeight alpha beta) : ℂ) *
      star (Real.sqrt (blockWeight alpha beta) : ℂ) = blockWeight alpha beta := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    norm_cast
    exact Real.mul_self_sqrt (div_nonneg (mul_nonneg hKA.le hKB.le) hN.le)
  refine ⟨hU, hV, hC, ?_, ?_⟩
  · rw [hA, hC, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hsq]
    congr 1
    calc
      (U * Vᴴ) * (V * Uᴴ) = U * (Vᴴ * V) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hV, Matrix.mul_one]
  · rw [hB, ← hreal, hC, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    have hsq' : star (Real.sqrt (blockWeight alpha beta) : ℂ) *
        (Real.sqrt (blockWeight alpha beta) : ℂ) = blockWeight alpha beta := by
      rw [mul_comm, hsq]
    rw [hsq']
    congr 1
    calc
      (V * Uᴴ) * (U * Vᴴ) = V * (Uᴴ * U) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hU, Matrix.mul_one]

/-- Flat spectra are extracted from the actual reductions, including ambient zero directions. -/
theorem actual_flat_reductions (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    blockWeight alpha beta = (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ ∧
    Matrix.trace (actualReducedA alpha beta) = 1 ∧
    Matrix.trace (actualReducedB alpha beta) = 1 ∧
    (actualCoefficient alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (actualReducedA alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (actualReducedB alpha beta).rank = Fintype.card (BlockQuotient alpha beta) ∧
    (∃ hA : (actualReducedA alpha beta).PosSemidef,
      (∀ i, hA.isHermitian.eigenvalues i = blockWeight alpha beta ∨
        hA.isHermitian.eigenvalues i = 0) ∧
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i =
        blockWeight alpha beta)).card = Fintype.card (BlockQuotient alpha beta) ∧
      (Finset.univ.filter (fun i => hA.isHermitian.eigenvalues i = 0)).card =
        Fintype.card A - Fintype.card (BlockQuotient alpha beta)) ∧
    (∃ hB : (actualReducedB alpha beta).PosSemidef,
      (∀ i, hB.isHermitian.eigenvalues i = blockWeight alpha beta ∨
        hB.isHermitian.eigenvalues i = 0) ∧
      (Finset.univ.filter (fun i => hB.isHermitian.eigenvalues i =
        blockWeight alpha beta)).card = Fintype.card (BlockQuotient alpha beta) ∧
      (Finset.univ.filter (fun i => hB.isHermitian.eigenvalues i = 0)).card =
        Fintype.card B - Fintype.card (BlockQuotient alpha beta)) := by
  classical
  obtain ⟨hU, hV, hC, hA, hB⟩ := actual_block_matrices alpha beta hpair
  let U := leftVectors alpha beta
  let V := rightVectors alpha beta
  let w := blockWeight alpha beta
  have hw : 0 < w := by
    exact div_pos (mul_pos (by exact_mod_cast Fintype.card_pos)
      (by exact_mod_cast Fintype.card_pos)) (by exact_mod_cast Fintype.card_pos)
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hcounts : Fintype.card G = Fintype.card (BlockQuotient alpha beta) *
      Fintype.card alpha.ker * Fintype.card beta.ker := by
    simpa only [Nat.card_eq_fintype_card] using
      (kernel_quotient_normalization alpha beta hpair).2.2
  have hwinv : w = (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ := by
    dsimp [w, blockWeight]
    rw [hcounts]
    push_cast
    have ha : (Fintype.card alpha.ker : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := alpha.ker)).ne'
    have hb : (Fintype.card beta.ker : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := beta.ker)).ne'
    field_simp [ha, hb]
  have hwR : (w : ℂ) * Fintype.card (BlockQuotient alpha beta) = 1 := by
    rw [hwinv]
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast
      (Fintype.card_pos (α := BlockQuotient alpha beta)).ne')
  have htraceA : Matrix.trace (actualReducedA alpha beta) = 1 := by
    rw [hA, Matrix.trace_smul, Matrix.trace_mul_comm, hU, Matrix.trace_one]
    exact hwR
  have htraceB : Matrix.trace (actualReducedB alpha beta) = 1 := by
    rw [hB, Matrix.trace_smul, Matrix.trace_mul_comm, hV, Matrix.trace_one]
    exact hwR
  have hrankA : (actualReducedA alpha beta).rank =
      Fintype.card (BlockQuotient alpha beta) := by
    rw [hA, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero hwC), Matrix.rank_self_mul_conjTranspose,
      ← Matrix.rank_conjTranspose_mul_self (leftVectors alpha beta), hU, Matrix.rank_one]
  have hrankB : (actualReducedB alpha beta).rank =
      Fintype.card (BlockQuotient alpha beta) := by
    rw [hB, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero hwC), Matrix.rank_self_mul_conjTranspose,
      ← Matrix.rank_conjTranspose_mul_self (rightVectors alpha beta), hV, Matrix.rank_one]
  have hAA : actualReducedA alpha beta =
      actualCoefficient alpha beta * (actualCoefficient alpha beta)ᴴ := by ext; rfl
  have hrankC : (actualCoefficient alpha beta).rank =
      Fintype.card (BlockQuotient alpha beta) := by
    rw [← Matrix.rank_self_mul_conjTranspose, ← hAA, hrankA]
  have hposA : (actualReducedA alpha beta).PosSemidef := by
    rw [hAA]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hposB : (actualReducedB alpha beta).PosSemidef := by
    rw [hB]
    exact (Matrix.posSemidef_self_mul_conjTranspose V).smul
      (show (0 : ℂ) ≤ (w : ℂ) by exact_mod_cast hw.le)
  have hquadA : actualReducedA alpha beta * actualReducedA alpha beta =
      (w : ℂ) • actualReducedA alpha beta := by
    simp only [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    calc
      (U * Uᴴ) * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ := by simp [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hU, Matrix.mul_one]
  have hquadB : actualReducedB alpha beta * actualReducedB alpha beta =
      (w : ℂ) • actualReducedB alpha beta := by
    simp only [hB, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have heigsA (i : A) : hposA.isHermitian.eigenvalues i = w ∨
      hposA.isHermitian.eigenvalues i = 0 := by
    let e := Unitary.conjStarAlgAut ℂ (Matrix A A ℂ)
      (star hposA.isHermitian.eigenvectorUnitary)
    have hd := congrArg e hquadA
    rw [map_mul, map_smul, hposA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary] at hd
    have hi := congrArg (fun M : Matrix A A ℂ => M i i) hd
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, smul_eq_mul, Function.comp_apply] at hi
    have hr : hposA.isHermitian.eigenvalues i * hposA.isHermitian.eigenvalues i =
        w * hposA.isHermitian.eigenvalues i := by
      simpa using congrArg Complex.re hi
    have hz : hposA.isHermitian.eigenvalues i *
        (hposA.isHermitian.eigenvalues i - w) = 0 := by nlinarith [hr]
    rcases mul_eq_zero.mp hz with hzero | heq
    · exact Or.inr hzero
    · exact Or.inl (sub_eq_zero.mp heq)
  have heigsB (i : B) : hposB.isHermitian.eigenvalues i = w ∨
      hposB.isHermitian.eigenvalues i = 0 := by
    let e := Unitary.conjStarAlgAut ℂ (Matrix B B ℂ)
      (star hposB.isHermitian.eigenvectorUnitary)
    have hd := congrArg e hquadB
    rw [map_mul, map_smul, hposB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary] at hd
    have hi := congrArg (fun M : Matrix B B ℂ => M i i) hd
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, smul_eq_mul, Function.comp_apply] at hi
    have hr : hposB.isHermitian.eigenvalues i * hposB.isHermitian.eigenvalues i =
        w * hposB.isHermitian.eigenvalues i := by
      simpa using congrArg Complex.re hi
    have hz : hposB.isHermitian.eigenvalues i *
        (hposB.isHermitian.eigenvalues i - w) = 0 := by nlinarith [hr]
    rcases mul_eq_zero.mp hz with hzero | heq
    · exact Or.inr hzero
    · exact Or.inl (sub_eq_zero.mp heq)
  have hsuppA : (Finset.univ.filter (fun i => hposA.isHermitian.eigenvalues i ≠ 0)).card =
      Fintype.card (BlockQuotient alpha beta) := by
    rw [← Fintype.card_subtype, ← hposA.isHermitian.rank_eq_card_non_zero_eigs, hrankA]
  have hsuppB : (Finset.univ.filter (fun i => hposB.isHermitian.eigenvalues i ≠ 0)).card =
      Fintype.card (BlockQuotient alpha beta) := by
    rw [← Fintype.card_subtype, ← hposB.isHermitian.rank_eq_card_non_zero_eigs, hrankB]
  refine ⟨hwinv, htraceA, htraceB, hrankC, hrankA, hrankB,
    ⟨hposA, heigsA, ?_, ?_⟩, ⟨hposB, heigsB, ?_, ?_⟩⟩
  · convert hsuppA using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change hposA.isHermitian.eigenvalues i = w ↔ hposA.isHermitian.eigenvalues i ≠ 0
    rcases heigsA i with hi | hi <;> simp [hi, hw.ne', hw.ne'.symm]
  · have hz : Finset.univ.filter (fun i => hposA.isHermitian.eigenvalues i = 0) =
        Finset.univ \ Finset.univ.filter (fun i => hposA.isHermitian.eigenvalues i ≠ 0) := by
      ext i; simp
    rw [hz, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_univ, hsuppA]
  · convert hsuppB using 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change hposB.isHermitian.eigenvalues i = w ↔ hposB.isHermitian.eigenvalues i ≠ 0
    rcases heigsB i with hi | hi <;> simp [hi, hw.ne', hw.ne'.symm]
  · have hz : Finset.univ.filter (fun i => hposB.isHermitian.eigenvalues i = 0) =
        Finset.univ \ Finset.univ.filter (fun i => hposB.isHermitian.eigenvalues i ≠ 0) := by
      ext i; simp
    rw [hz, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_univ, hsuppB]

/- The joint matrix is the actual outer product, so its state properties are
   consequences of the coefficient normalization rather than extra axioms. -/
theorem actual_joint_state (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    (actualJoint alpha beta).PosSemidef ∧
      (actualJoint alpha beta).IsHermitian ∧
      Matrix.trace (actualJoint alpha beta) = 1 ∧
      actualJoint alpha beta * actualJoint alpha beta = actualJoint alpha beta ∧
      (actualJoint alpha beta).rank = 1 := by
  classical
  obtain ⟨_, htraceA, _, _, _, _, _, _⟩ := actual_flat_reductions alpha beta hpair
  let psi : A × B → ℂ := fun p => actualCoefficient alpha beta p.1 p.2
  have houter : actualJoint alpha beta = Matrix.vecMulVec psi (star psi) := by
    ext p r
    rfl
  have htrace : Matrix.trace (actualJoint alpha beta) = 1 := by
    rw [← trace_partialTraceRight (actualJoint alpha beta)]
    exact htraceA
  have hnorm : star psi ⬝ᵥ psi = 1 := by
    simpa [houter, Matrix.trace_vecMulVec, dotProduct, mul_comm] using htrace
  have hpos : (actualJoint alpha beta).PosSemidef := by
    rw [houter]
    exact Matrix.posSemidef_vecMulVec_self_star psi
  have hherm : (actualJoint alpha beta).IsHermitian := hpos.isHermitian
  have hidem : actualJoint alpha beta * actualJoint alpha beta = actualJoint alpha beta := by
    rw [houter, Matrix.vecMulVec_mul_vecMulVec, hnorm, one_smul]
  have hpsi : ∃ p, psi p ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : psi = 0 := funext h
    have : (0 : ℂ) = 1 := by simpa [hz, dotProduct] using hnorm
    exact zero_ne_one this
  have hrank_pos : 0 < (actualJoint alpha beta).rank := by
    rw [houter, Matrix.rank_eq_finrank_span_cols]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    obtain ⟨p, hp⟩ := hpsi
    let col : Submodule.span ℂ (Set.range (Matrix.vecMulVec psi (star psi)).col) :=
      ⟨(Matrix.vecMulVec psi (star psi)).col p,
        Submodule.subset_span ⟨p, rfl⟩⟩
    refine ⟨col, ?_⟩
    intro hz
    have hentry := congrFun (congrArg Subtype.val hz) p
    have hmul : psi p * star (psi p) = 0 := by
      simpa [col, Matrix.vecMulVec_apply] using hentry
    exact (mul_ne_zero hp (star_ne_zero.mpr hp)) hmul
  have hrank_le : (actualJoint alpha beta).rank ≤ 1 := by
    rw [houter]
    exact Matrix.rank_vecMulVec_le psi (star psi)
  refine ⟨hpos, hherm, htrace, hidem, ?_⟩
  omega

/-- The actual reduced states have the complete flat spectrum and its entropy. -/
theorem actual_reduced_entropy (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x))) :
    let rhoA : DensityState A := by
      classical
      obtain ⟨_, htraceA, _, _, _, _, hspecA, _⟩ :=
        actual_flat_reductions alpha beta hpair
      let hA := Classical.choose hspecA
      refine ⟨CStarMatrix.ofMatrix (actualReducedA alpha beta), ?_, ?_⟩
      · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hA.nonneg
      · exact htraceA
    let rhoB : DensityState B := by
      classical
      obtain ⟨_, _, htraceB, _, _, _, _, hspecB⟩ :=
        actual_flat_reductions alpha beta hpair
      let hB := Classical.choose hspecB
      refine ⟨CStarMatrix.ofMatrix (actualReducedB alpha beta), ?_, ?_⟩
      · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hB.nonneg
      · exact htraceB
    vonNeumannEntropy rhoA = Real.log (Fintype.card (BlockQuotient alpha beta)) ∧
      vonNeumannEntropy rhoB = Real.log (Fintype.card (BlockQuotient alpha beta)) := by
  classical
  obtain ⟨hw, htraceA, htraceB, _, _, _, hspecA, hspecB⟩ :=
    actual_flat_reductions alpha beta hpair
  obtain ⟨hposA, heigsA, hcountA, _⟩ := hspecA
  obtain ⟨hposB, heigsB, hcountB, _⟩ := hspecB
  let rhoA : DensityState A := by
    refine ⟨CStarMatrix.ofMatrix (actualReducedA alpha beta), ?_, ?_⟩
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hposA.nonneg
    · exact htraceA
  let rhoB : DensityState B := by
    refine ⟨CStarMatrix.ofMatrix (actualReducedB alpha beta), ?_, ?_⟩
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hposB.nonneg
    · exact htraceB
  have hspecA' (i : Fin (Fintype.card A)) :
      D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum rhoA i =
        hposA.isHermitian.eigenvalues₀ i := by
    have hmat : densityMatrix rhoA = actualReducedA alpha beta := by
      ext j k
      rfl
    unfold D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum
    simp only [hmat]
  have hspecB' (i : Fin (Fintype.card B)) :
      D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum rhoB i =
        hposB.isHermitian.eigenvalues₀ i := by
    have hmat : densityMatrix rhoB = actualReducedB alpha beta := by
      ext j k
      rfl
    unfold D5.S3.Quantum.Sharpness.FreeNegentropyBudget.stateSpectrum
    simp only [hmat]
  have hcardA : (Fintype.card A : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hcardB : (Fintype.card B : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hR : (Fintype.card (BlockQuotient alpha beta) : ℝ) > 0 :=
    by exact_mod_cast Fintype.card_pos
  have hflat_entropyA (w : ℝ) (hw' : w =
      (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹)
      (hpos : (actualReducedA alpha beta).PosSemidef)
      (heigs : ∀ i, hpos.isHermitian.eigenvalues i = w ∨
        hpos.isHermitian.eigenvalues i = 0)
      (hcount : (Finset.univ.filter (fun i =>
        hpos.isHermitian.eigenvalues i = w)).card = Fintype.card (BlockQuotient alpha beta))
      (hwpos : 0 < w) :
      ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    have hpoint (i : A) : Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        if hpos.isHermitian.eigenvalues i = w then Real.negMulLog w else 0 := by
      rcases heigs i with hi | hi
      · simp [hi]
      · have hne : (0 : ℝ) ≠ w := ne_of_lt hwpos
        simp [hi, hne]
    have hsum : ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        ((Finset.univ.filter (fun i => hpos.isHermitian.eigenvalues i = w)).card : ℝ) *
          Real.negMulLog w := by
      simp_rw [hpoint]
      rw [Finset.sum_ite]
      simp
    rw [hsum, hcount]
    have hwform : Real.negMulLog w =
        (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ *
          Real.log (Fintype.card (BlockQuotient alpha beta)) := by
      rw [Real.negMulLog, hw', Real.log_inv]
      ring
    rw [hwform]
    field_simp
  have hflat_entropyB (w : ℝ) (hw' : w =
      (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹)
      (hpos : (actualReducedB alpha beta).PosSemidef)
      (heigs : ∀ i, hpos.isHermitian.eigenvalues i = w ∨
        hpos.isHermitian.eigenvalues i = 0)
      (hcount : (Finset.univ.filter (fun i =>
        hpos.isHermitian.eigenvalues i = w)).card = Fintype.card (BlockQuotient alpha beta))
      (hwpos : 0 < w) :
      ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    have hpoint (i : B) : Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        if hpos.isHermitian.eigenvalues i = w then Real.negMulLog w else 0 := by
      rcases heigs i with hi | hi
      · simp [hi]
      · have hne : (0 : ℝ) ≠ w := ne_of_lt hwpos
        simp [hi, hne]
    have hsum : ∑ i, Real.negMulLog (hpos.isHermitian.eigenvalues i) =
        ((Finset.univ.filter (fun i => hpos.isHermitian.eigenvalues i = w)).card : ℝ) *
          Real.negMulLog w := by
      simp_rw [hpoint]
      rw [Finset.sum_ite]
      simp
    rw [hsum, hcount]
    have hwform : Real.negMulLog w =
        (Fintype.card (BlockQuotient alpha beta) : ℝ)⁻¹ *
          Real.log (Fintype.card (BlockQuotient alpha beta)) := by
      rw [Real.negMulLog, hw', Real.log_inv]
      ring
    rw [hwform]
    field_simp
  have hEA : vonNeumannEntropy rhoA =
      Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    rw [D5.S3.Quantum.Sharpness.FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum]
    unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
    simp_rw [hspecA']
    rw [← RHLinalg.sum_eigenvalues_reindex hposA.isHermitian Real.negMulLog]
    exact hflat_entropyA (blockWeight alpha beta) hw hposA
      heigsA hcountA (by
        exact div_pos (mul_pos (by exact_mod_cast Fintype.card_pos)
          (by exact_mod_cast Fintype.card_pos)) (by exact_mod_cast Fintype.card_pos))
  have hEB : vonNeumannEntropy rhoB =
      Real.log (Fintype.card (BlockQuotient alpha beta)) := by
    rw [D5.S3.Quantum.Sharpness.FreeNegentropyBudget.von_neumann_entropy_eq_shannon_state_spectrum]
    unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
    simp_rw [hspecB']
    rw [← RHLinalg.sum_eigenvalues_reindex hposB.isHermitian Real.negMulLog]
    exact hflat_entropyB (blockWeight alpha beta) hw hposB
      heigsB hcountB (by
        exact div_pos (mul_pos (by exact_mod_cast Fintype.card_pos)
          (by exact_mod_cast Fintype.card_pos)) (by exact_mod_cast Fintype.card_pos))
  simpa [rhoA, rhoB] using ⟨hEA, hEB⟩

end D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum

#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.paired_block_iff
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_coefficient_block
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.right_block_card
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.kernel_quotient_normalization
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.readout_block_partitions
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_block_matrices
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_flat_reductions
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_joint_state
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutSpectrum.actual_reduced_entropy
