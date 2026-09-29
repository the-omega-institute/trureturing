/- GID: D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite additive readouts give source cosets and block matrices. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Sharpness.FreeNegentropyBudget
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Tactic

/- Source sums and quotient cosets determine the actual coefficient and partial-trace blocks. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

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

noncomputable def actualSourceKet (alpha : G →+ A) (beta : G →+ B) : A × B → ℂ :=
  (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ •
    ∑ x : G, Pi.single (alpha x, beta x) (1 : ℂ)

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



/-- The actual paired readout bijects each source coset onto its two label blocks. -/
theorem source_coset_product (alpha : G →+ A) (beta : G →+ B)
    (hpair : Function.Injective (fun x : G => (alpha x, beta x)))
    (q : BlockQuotient alpha beta) :
    ∃ e : {x : G // (QuotientAddGroup.mk' (kernelSum alpha beta)) x = q} ≃
        ({a : A // leftBlock alpha beta q a} × {b : B // rightBlock alpha beta q b}),
      ∀ x, (e x).1.1 = alpha x.1 ∧ (e x).2.1 = beta x.1 := by
  classical
  let f : {x : G // (QuotientAddGroup.mk' (kernelSum alpha beta)) x = q} →
      ({a : A // leftBlock alpha beta q a} × {b : B // rightBlock alpha beta q b}) :=
    fun x => (⟨alpha x.1, x.1, x.2, rfl⟩, ⟨beta x.1, x.1, x.2, rfl⟩)
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hpair (Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h))
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨a, x, hxq, hxa⟩, ⟨b, y, hyq, hyb⟩⟩
    have hxy : x - y ∈ kernelSum alpha beta :=
      QuotientAddGroup.eq_iff_sub_mem.mp (hxq.trans hyq.symm)
    obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp hxy
    have hzq : (QuotientAddGroup.mk' (kernelSum alpha beta)) (x - s) = q := by
      rw [← hxq]
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have heq : (x - s) - x = -s := by abel
      rw [heq]
      exact AddSubgroup.mem_sup_left (alpha.ker.neg_mem hs)
    refine ⟨⟨x - s, hzq⟩, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · change alpha (x - s) = a
      simpa [map_sub, show alpha s = 0 from hs] using hxa
    · change beta (x - s) = b
      have hz : x - s = y + t := by
        apply (sub_eq_iff_eq_add).2
        calc
          x = (x - y) + y := by abel
          _ = (s + t) + y := by rw [← hst]
          _ = (y + t) + s := by abel
      rw [hz, map_add, show beta t = 0 from ht, add_zero]
      exact hyb
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => ⟨rfl, rfl⟩⟩

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
      (rightVectors alpha beta * (rightVectors alpha beta)ᴴ) ∧
    (∀ q, (actualReducedA alpha beta).mulVec ((leftVectors alpha beta).col q) =
      (blockWeight alpha beta : ℂ) • (leftVectors alpha beta).col q) ∧
    (∀ q, (actualReducedB alpha beta).mulVec ((rightVectors alpha beta).col q) =
      (blockWeight alpha beta : ℂ) • (rightVectors alpha beta).col q) ∧
    (∀ v : A → ℂ, ((leftVectors alpha beta)ᴴ).mulVec v = 0 →
      (actualReducedA alpha beta).mulVec v = 0) ∧
    (∀ v : B → ℂ, ((rightVectors alpha beta)ᴴ).mulVec v = 0 →
      (actualReducedB alpha beta).mulVec v = 0) ∧
    (leftVectors alpha beta * (leftVectors alpha beta)ᴴ) *
      (leftVectors alpha beta * (leftVectors alpha beta)ᴴ) =
        leftVectors alpha beta * (leftVectors alpha beta)ᴴ ∧
    (leftVectors alpha beta * (leftVectors alpha beta)ᴴ).IsHermitian ∧
    (rightVectors alpha beta * (rightVectors alpha beta)ᴴ) *
      (rightVectors alpha beta * (rightVectors alpha beta)ᴴ) =
        rightVectors alpha beta * (rightVectors alpha beta)ᴴ ∧
    (rightVectors alpha beta * (rightVectors alpha beta)ᴴ).IsHermitian ∧
    ((∀ a q r, leftBlock alpha beta q a → leftBlock alpha beta r a → q = r) ∧
    (∀ b q r, rightBlock alpha beta q b → rightBlock alpha beta r b → q = r) ∧
    (∀ a, (∃ q, leftBlock alpha beta q a) ↔ a ∈ Set.range alpha) ∧
    (∀ b, (∃ q, rightBlock alpha beta q b) ↔ b ∈ Set.range beta)) ∧
    (∀ q, (Finset.univ.filter (leftBlock alpha beta q)).card = Fintype.card beta.ker) ∧
    (∀ q, (Finset.univ.filter (rightBlock alpha beta q)).card = Fintype.card alpha.ker) ∧
    (∀ x a, leftBlock alpha beta ((QuotientAddGroup.mk' (kernelSum alpha beta)) x) a ↔
      ∃ t : beta.ker, a = alpha x + alpha t.1) ∧
    (∀ x b, rightBlock alpha beta ((QuotientAddGroup.mk' (kernelSum alpha beta)) x) b ↔
      ∃ s : alpha.ker, b = beta x + beta s.1) ∧
    actualReducedA alpha beta * actualReducedA alpha beta =
      (blockWeight alpha beta : ℂ) • actualReducedA alpha beta ∧
    actualReducedB alpha beta * actualReducedB alpha beta =
      (blockWeight alpha beta : ℂ) • actualReducedB alpha beta ∧
    (∀ a c, actualReducedA alpha beta a c =
      (Fintype.card alpha.ker : ℂ) / Fintype.card G *
        ∑ q : BlockQuotient alpha beta,
          if leftBlock alpha beta q a ∧ leftBlock alpha beta q c then (1 : ℂ) else 0) ∧
    (∀ b d, actualReducedB alpha beta b d =
      (Fintype.card beta.ker : ℂ) / Fintype.card G *
        ∑ q : BlockQuotient alpha beta,
          if rightBlock alpha beta q b ∧ rightBlock alpha beta q d then (1 : ℂ) else 0) ∧
    Fintype.card (BlockQuotient alpha beta) ≤ min (Fintype.card A) (Fintype.card B) := by
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
  have hpartition : (∀ a q r, leftBlock alpha beta q a → leftBlock alpha beta r a → q = r) ∧
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
  have hredA : actualReducedA alpha beta = (blockWeight alpha beta : ℂ) • (U * Uᴴ) := by
    rw [hA, hC, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hsq]
    congr 1
    calc
      (U * Vᴴ) * (V * Uᴴ) = U * (Vᴴ * V) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hV, Matrix.mul_one]
  have hredB : actualReducedB alpha beta = (blockWeight alpha beta : ℂ) • (V * Vᴴ) := by
    rw [hB, ← hreal, hC, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
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
  refine ⟨hU, hV, hC, hredA, hredB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hpartition, hleft, hright, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have hinner : (Uᴴ).mulVec (U.col q) = Pi.single q (1 : ℂ) := by
      rw [← Matrix.mulVec_single_one U q, Matrix.mulVec_mulVec, hU,
        Matrix.one_mulVec]
    rw [hredA, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hinner, Matrix.mulVec_single_one]
  · intro q
    have hinner : (Vᴴ).mulVec (V.col q) = Pi.single q (1 : ℂ) := by
      rw [← Matrix.mulVec_single_one V q, Matrix.mulVec_mulVec, hV,
        Matrix.one_mulVec]
    rw [hredB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hinner, Matrix.mulVec_single_one]
  · intro v hv
    rw [hredA, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero]
  · intro v hv
    rw [hredB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero]
  · calc
      (U * Uᴴ) * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hU, Matrix.mul_one]
  · exact Matrix.isHermitian_mul_conjTranspose_self U
  · calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  · exact Matrix.isHermitian_mul_conjTranspose_self V
  · intro x a
    constructor
    · rintro ⟨y, hyq, hya⟩
      obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp
        (QuotientAddGroup.eq_iff_sub_mem.mp hyq)
      have hy : y = x + s + t := by
        calc
          y = x + (y - x) := by abel
          _ = x + (s + t) := by rw [← hst]
          _ = x + s + t := by abel
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa [hy, map_add, show alpha s = 0 from hs] using hya.symm
    · rintro ⟨t, ha⟩
      refine ⟨x + t.1, ?_, ?_⟩
      · apply QuotientAddGroup.eq_iff_sub_mem.mpr
        simpa only [add_sub_cancel_left, kernelSum] using
          (AddSubgroup.mem_sup_right t.2 : t.1 ∈ alpha.ker ⊔ beta.ker)
      · simpa only [map_add] using ha.symm
  · intro x b
    constructor
    · rintro ⟨y, hyq, hyb⟩
      obtain ⟨s, hs, t, ht, hst⟩ := AddSubgroup.mem_sup.mp
        (QuotientAddGroup.eq_iff_sub_mem.mp hyq)
      have hy : y = x + s + t := by
        calc
          y = x + (y - x) := by abel
          _ = x + (s + t) := by rw [← hst]
          _ = x + s + t := by abel
      refine ⟨⟨s, hs⟩, ?_⟩
      simpa [hy, map_add, show beta t = 0 from ht] using hyb.symm
    · rintro ⟨s, hb⟩
      refine ⟨x + s.1, ?_, ?_⟩
      · apply QuotientAddGroup.eq_iff_sub_mem.mpr
        simpa only [add_sub_cancel_left, kernelSum] using
          (AddSubgroup.mem_sup_left s.2 : s.1 ∈ alpha.ker ⊔ beta.ker)
      · simpa only [map_add] using hb.symm
  · simp only [hredA, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    calc
      (U * Uᴴ) * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Uᴴ := by rw [hU, Matrix.mul_one]
  · simp only [hredB, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  · intro a c
    have hs : (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ) *
        (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ) = Fintype.card beta.ker := by
      norm_cast
      exact Real.mul_self_sqrt hKB.le
    have hscaleA : (blockWeight alpha beta : ℂ) *
        (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (Fintype.card beta.ker : ℝ) : ℂ)⁻¹ =
        (Fintype.card alpha.ker : ℂ) / Fintype.card G := by
      rw [mul_assoc, ← mul_inv, hs]
      unfold blockWeight
      push_cast
      field_simp
    rw [hredA]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      U, leftVectors, smul_eq_mul, map_mul, map_inv₀, Complex.star_def,
      Complex.conj_ofReal, apply_ite, map_one, map_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases ha : leftBlock alpha beta q a <;>
      by_cases hc : leftBlock alpha beta q c <;>
      simp only [ha, hc, and_self, true_and, false_and, and_false, if_true, if_false,
        mul_one, mul_zero, zero_mul, ← mul_assoc]
    exact hscaleA
  · intro b d
    have hs : (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ) *
        (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ) = Fintype.card alpha.ker := by
      norm_cast
      exact Real.mul_self_sqrt hKA.le
    have hscaleB : (blockWeight alpha beta : ℂ) *
        (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (Fintype.card alpha.ker : ℝ) : ℂ)⁻¹ =
        (Fintype.card beta.ker : ℂ) / Fintype.card G := by
      rw [mul_assoc, ← mul_inv, hs]
      unfold blockWeight
      push_cast
      field_simp
      <;> ring
    rw [hredB]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      V, rightVectors, smul_eq_mul, map_mul, map_inv₀, Complex.star_def,
      Complex.conj_ofReal, apply_ite, map_one, map_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hb : rightBlock alpha beta q b <;>
      by_cases hd : rightBlock alpha beta q d <;>
      simp only [hb, hd, and_self, true_and, false_and, and_false, if_true, if_false,
        mul_one, mul_zero, zero_mul, ← mul_assoc]
    exact hscaleB
  · apply le_min
    · have h := U.rank_le_card_height
      rw [← Matrix.rank_conjTranspose_mul_self U, hU, Matrix.rank_one] at h
      exact h
    · have h := V.rank_le_card_height
      rw [← Matrix.rank_conjTranspose_mul_self V, hV, Matrix.rank_one] at h
      exact h
end D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.paired_block_iff
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_coefficient_block
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.right_block_card
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.source_coset_product
#print axioms D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks.actual_block_matrices
