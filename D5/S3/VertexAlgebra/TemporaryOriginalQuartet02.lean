import D5.S3.VertexAlgebra.TemporaryOriginalQuartet01

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def down : Fock ℂ := c 1 vacuum

def up : Fock ℂ := c 0 down

def toggleOne (subset : Finset ℕ) : Finset ℕ :=
  if 1 ∈ subset then subset.erase 1 else insert 1 subset

def polarizationSign (subset : Finset ℕ) : ℂ :=
  (-1) ^ (subset.filter fun site => 1 < site).card

def polarizedBasis (subset : Finset ℕ) : Fock ℂ :=
  polarizationSign subset • Finsupp.single (toggleOne subset) 1

def downCreator (site : ℕ) : Module.End ℂ (Fock ℂ) :=
  if site = 1 then b (-1) else create site

def downWord (subset : Finset ℕ) : Module.End ℂ (Fock ℂ) :=
  ((subset.sort (· ≤ ·)).map downCreator).prod

def etaCount (subset : Finset ℕ) : ℕ :=
  (subset.filter fun site => site = 1 ∨ site % 2 = 0).card

def thetaCount (subset : Finset ℕ) : ℕ :=
  (subset.filter fun site => site % 2 = 1 ∧ site ≠ 1 ∧ site ≠ 3).card

def epsilonCount (subset : Finset ℕ) : ℤ := if 3 ∈ subset then 1 else 0

def polarizedWeight (site : ℕ) : ℤ :=
  if site = 1 then 1 else BcGhostLZeroSpectrum.siteWeight site

def polarizedLevel (subset : Finset ℕ) : ℤ := ∑ site ∈ subset, polarizedWeight site

theorem down_original_basis : down = Finsupp.single {1} (1 : ℂ) := by
  simp [down, c, vacuum, create, createBasis, sign]

theorem up_original_basis : up = -Finsupp.single {1, 3} (1 : ℂ) := by
  rw [up, down_original_basis]
  norm_num [c, create, createBasis, sign, Finset.filter_insert, Finset.filter_singleton,
    Finsupp.smul_single, Finset.insert_comm]
  congr 1
  decide

theorem toggleOne_insert (site : ℕ) (subset : Finset ℕ) (different : site ≠ 1) :
    toggleOne (insert site subset) = insert site (toggleOne subset) := by
  by_cases present : 1 ∈ subset
  · simp [toggleOne, present, different, Ne.symm different,
      Finset.erase_insert_of_ne different]
  · simp [toggleOne, present, different, Ne.symm different, Finset.insert_comm]

theorem toggleOne_mem (site : ℕ) (subset : Finset ℕ) (different : site ≠ 1) :
    site ∈ toggleOne subset ↔ site ∈ subset := by
  by_cases present : 1 ∈ subset <;> simp [toggleOne, present, different]

theorem sign_min (site : ℕ) (subset : Finset ℕ)
    (minimum : ∀ other ∈ subset, site < other) : sign (K := ℂ) site subset = 1 := by
  have emptyFilter : subset.filter (fun other => other < site) = ∅ := by
    apply Finset.filter_false_of_mem
    intro other member
    exact not_lt.mpr (minimum other member).le
  simp [sign, emptyFilter]

theorem signed_down_word (subset : Finset ℕ) : downWord subset down = polarizedBasis subset := by
  classical
  induction subset using Finset.induction_on_min with
  | empty => simp [downWord, polarizedBasis, polarizationSign, toggleOne, down_original_basis]
  | @insert site subset minimum inductionHypothesis =>
      have absent : site ∉ subset := fun member => (lt_irrefl site) (minimum site member)
      have wordStep : downWord (insert site subset) = downCreator site * downWord subset := by
        simp [downWord, Finset.sort_insert (· ≤ ·)
          (fun other member => (minimum other member).le) absent]
      rw [wordStep, Module.End.mul_apply, inductionHypothesis]
      by_cases switchedSite : site = 1
      · subst site
        have noOne : 1 ∉ subset := absent
        have originalSign : sign (K := ℂ) 1 (insert 1 subset) = 1 := by
          have emptyFilter : (insert 1 subset).filter (fun other => other < 1) = ∅ := by
            apply Finset.filter_false_of_mem
            intro other member
            rcases Finset.mem_insert.mp member with rfl | member
            · omega
            · exact not_lt.mpr (minimum other member).le
          rw [sign, emptyFilter]
          norm_num
        simp [downCreator, b, polarizedBasis, toggleOne, noOne, annihilate,
          annihilateBasis, originalSign, polarizationSign, Finset.filter_insert]
      · have stillAbsent : site ∉ toggleOne subset := by
          simpa only [toggleOne_mem site subset switchedSite] using absent
        have toggledInsertion := toggleOne_insert site subset switchedSite
        by_cases aboveOne : 1 < site
        · have noOne : 1 ∉ subset := by
            intro member
            have impossible := minimum 1 member
            omega
          have changedSign : sign (K := ℂ) site (toggleOne subset) = -1 := by
            calc
              _ = -sign (K := ℂ) site subset := by
                simp [toggleOne, noOne, sign, Finset.filter_insert, aboveOne,
                  pow_succ, mul_comm]
              _ = -1 := by rw [sign_min site subset minimum]
          have signStep : polarizationSign (insert site subset) = -polarizationSign subset := by
            simp [polarizationSign, Finset.filter_insert, aboveOne, absent,
              pow_succ, mul_comm]
          simp [downCreator, switchedSite, polarizedBasis, create,
            createBasis, stillAbsent, changedSign, toggledInsertion, signStep,
            Finsupp.smul_single, smul_smul]
        · have siteZero : site = 0 := by omega
          subst site
          have unchangedSign : sign (K := ℂ) 0 (toggleOne subset) = 1 := by simp [sign]
          have signStep : polarizationSign (insert 0 subset) = polarizationSign subset := by
            simp [polarizationSign, Finset.filter_insert]
          simp [downCreator, polarizedBasis, create, createBasis,
            stillAbsent, unchangedSign, toggledInsertion, signStep, Finsupp.smul_single]

theorem toggleOne_degree (subset : Finset ℕ) :
    BcGhostNumber.degree (toggleOne subset) =
      1 + epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) := by
  classical
  let evenSites := subset.filter (fun site => site % 2 = 0)
  let thetaSites := subset.filter (fun site => site % 2 = 1 ∧ site ≠ 1 ∧ site ≠ 3)
  have evenAbsent : 1 ∉ evenSites := by simp [evenSites]
  have thetaAbsent : 3 ∉ thetaSites := by simp [thetaSites]
  have etaDecomposition : subset.filter (fun site => site = 1 ∨ site % 2 = 0) =
      if 1 ∈ subset then insert 1 evenSites else evenSites := by
    ext site
    by_cases present : 1 ∈ subset
    · simp only [if_pos present, Finset.mem_filter, Finset.mem_insert, evenSites]
      by_cases same : site = 1 <;> simp [same, present]
    · simp only [if_neg present, Finset.mem_filter, evenSites]
      by_cases same : site = 1 <;> simp [same, present]
  have oddDecomposition : ((subset.erase 1).filter fun site => site % 2 = 1) =
      if 3 ∈ subset then insert 3 thetaSites else thetaSites := by
    ext site
    by_cases present : 3 ∈ subset
    · simp only [if_pos present, Finset.mem_filter, Finset.mem_erase,
        Finset.mem_insert, thetaSites]
      by_cases same : site = 3 <;> simp [same, present] <;> tauto
    · simp only [if_neg present, Finset.mem_filter, Finset.mem_erase, thetaSites]
      by_cases same : site = 3 <;> simp [same, present] <;> tauto
  have erasedEven : ((subset.erase 1).filter fun site => site % 2 = 0) = evenSites := by
    ext site
    simp only [Finset.mem_filter, Finset.mem_erase, evenSites]
    constructor
    · tauto
    · intro member
      have different : site ≠ 1 := by intro equality; subst site; norm_num at member
      exact ⟨⟨different, member.1⟩, member.2⟩
  have degreeInsert (rest : Finset ℕ) (absent : 1 ∉ rest) :
      BcGhostNumber.degree (insert 1 rest) = BcGhostNumber.degree rest + 1 := by
    simp [BcGhostNumber.degree, Finset.filter_insert, absent]
    omega
  have toggleDegree : BcGhostNumber.degree (toggleOne subset) =
      BcGhostNumber.degree (subset.erase 1) + if 1 ∈ subset then 0 else 1 := by
    by_cases present : 1 ∈ subset
    · simp [toggleOne, present]
    · simp [toggleOne, present, degreeInsert subset present]
  rw [toggleDegree]
  simp only [BcGhostNumber.degree, oddDecomposition, erasedEven, etaCount,
    etaDecomposition, thetaCount, epsilonCount]
  by_cases onePresent : 1 ∈ subset <;> by_cases threePresent : 3 ∈ subset <;>
    simp [onePresent, threePresent, evenAbsent, thetaAbsent, evenSites, thetaSites] <;> omega

theorem toggleOne_energy (subset : Finset ℕ) :
    BcGhostLZeroSpectrum.energy (toggleOne subset) = -1 + polarizedLevel subset := by
  classical
  have sumErased : (∑ site ∈ subset.erase 1, polarizedWeight site) =
      BcGhostLZeroSpectrum.energy (subset.erase 1) := by
    apply Finset.sum_congr rfl
    intro site member
    simp only [polarizedWeight, if_neg (Finset.ne_of_mem_erase member)]
  have levelFormula : polarizedLevel subset =
      BcGhostLZeroSpectrum.energy (subset.erase 1) + if 1 ∈ subset then 1 else 0 := by
    by_cases present : 1 ∈ subset
    · calc
        _ = polarizedLevel (insert 1 (subset.erase 1)) := by rw [Finset.insert_erase present]
        _ = _ := by
          rw [polarizedLevel, Finset.sum_insert (by simp), sumErased]
          simp [polarizedWeight, present, add_comm]
    · have noErase : subset.erase 1 = subset := Finset.erase_eq_of_notMem present
      simpa [polarizedLevel, noErase, present] using sumErased
  rw [levelFormula]
  by_cases present : 1 ∈ subset
  · simp [toggleOne, present]
  · simp [toggleOne, present, BcGhostLZeroSpectrum.energy,
      BcGhostLZeroSpectrum.siteWeight, add_comm, add_left_comm]

theorem polarized_J (subset : Finset ℕ) :
    BcGhostNumber.J (K := ℂ) (downWord subset down) =
      ((1 + epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) : ℤ) : ℂ) •
        downWord subset down := by
  rw [signed_down_word]
  have diagonal (original : Finset ℕ) : BcGhostNumber.J (K := ℂ) (Finsupp.single original 1) =
      (BcGhostNumber.degree original : ℂ) • Finsupp.single original 1 := by
    simp [BcGhostNumber.J, Finsupp.smul_single]
  simp only [polarizedBasis, map_smul, diagonal, toggleOne_degree]
  rw [smul_comm]

theorem polarized_L_zero (subset : Finset ℕ) :
    L (K := ℂ) 0 (downWord subset down) =
      ((-1 + polarizedLevel subset : ℤ) : ℂ) • downWord subset down := by
  rw [signed_down_word]
  simp only [polarizedBasis, map_smul, BcGhostLZeroSpectrum.L_zero_single, toggleOne_energy]
  rw [smul_comm]

theorem original_b_zero_down_up : b (K := ℂ) 0 down = 0 ∧ b (K := ℂ) 0 up = down := by
  constructor
  · rw [down_original_basis]
    simp [b, annihilate, annihilateBasis]
  · rw [up_original_basis, down_original_basis]
    norm_num [b, annihilate, annihilateBasis, sign, Finset.filter_insert,
      Finset.filter_singleton, Finset.erase_insert_of_ne (by decide : (1 : ℕ) ≠ 3),
      Finsupp.smul_single, Finset.insert_comm]

theorem positive_modes_down (mode : ℤ) (positive : 0 < mode) :
    b (K := ℂ) mode down = 0 ∧ c (K := ℂ) mode down = 0 := by
  rw [down_original_basis]
  constructor
  · have branch : ¬ mode ≤ -2 := by omega
    have absent : 2 * (mode + 1).toNat + 1 ≠ 1 := by omega
    rw [b, if_neg branch]
    simp only [annihilate, Finsupp.linearCombination_single, one_smul,
      annihilateBasis, Finset.mem_singleton, if_neg absent]
  · by_cases creator : mode ≤ 1
    · have modeOne : mode = 1 := by omega
      subst mode
      simp [c, create, createBasis]
    · have absent : 2 * (mode - 2).toNat ≠ 1 := by omega
      simp [c, creator, annihilate, annihilateBasis, absent]

theorem polarizedWeight_bound (site : ℕ) :
    (if site = 3 then 0 else 1 : ℤ) ≤ polarizedWeight site := by
  by_cases switched : site = 1
  · subst site; norm_num [polarizedWeight]
  · by_cases even : site % 2 = 0
    · simp only [polarizedWeight, if_neg switched, BcGhostLZeroSpectrum.siteWeight,
        if_pos even]
      split_ifs <;> omega
    · have odd : site % 2 = 1 := by omega
      simp only [polarizedWeight, if_neg switched, BcGhostLZeroSpectrum.siteWeight,
        if_neg even]
      split_ifs <;> omega

theorem ghost_excitation_bound (subset : Finset ℕ) :
    ((etaCount subset + thetaCount subset : ℕ) : ℤ) ≤ polarizedLevel subset := by
  classical
  let etaSites := subset.filter (fun site => site = 1 ∨ site % 2 = 0)
  let thetaSites := subset.filter (fun site => site % 2 = 1 ∧ site ≠ 1 ∧ site ≠ 3)
  have partition : etaSites ∪ thetaSites = subset.erase 3 := by
    ext site
    simp only [etaSites, thetaSites, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    have parity : site % 2 = 0 ∨ site % 2 = 1 := by omega
    by_cases one : site = 1 <;> by_cases three : site = 3 <;> simp [one, three] <;> tauto
  have disjoint : Disjoint etaSites thetaSites := by
    apply Finset.disjoint_left.mpr
    intro site etaMember thetaMember
    simp only [etaSites, thetaSites, Finset.mem_filter] at etaMember thetaMember
    rcases etaMember.2 with one | even
    · exact thetaMember.2.2.1 one
    · omega
  have countIdentity : etaCount subset + thetaCount subset = (subset.erase 3).card := by
    rw [← partition, Finset.card_union_of_disjoint disjoint]
    rfl
  have erasedBound : ((subset.erase 3).card : ℤ) ≤
      ∑ site ∈ subset.erase 3, polarizedWeight site := by
    calc
      _ = ∑ site ∈ subset.erase 3, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun site member => by
        simpa only [if_neg (Finset.ne_of_mem_erase member)] using polarizedWeight_bound site)
  have wholeBound : (∑ site ∈ subset.erase 3, polarizedWeight site) = polarizedLevel subset := by
    by_cases present : 3 ∈ subset
    · calc
        _ = polarizedLevel (insert 3 (subset.erase 3)) := by
          simp [polarizedLevel, polarizedWeight, BcGhostLZeroSpectrum.siteWeight]
        _ = _ := by rw [Finset.insert_erase present]
    · simp [polarizedLevel, Finset.erase_eq_of_notMem present]
  rw [countIdentity, ← wholeBound]
  exact erasedBound

theorem ghost_auxiliary_bounds (subset : Finset ℕ) :
    -polarizedLevel subset ≤
      epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) ∧
    epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) ≤
      polarizedLevel subset + 1 := by
  have countsBound := ghost_excitation_bound subset
  have epsilonBound : 0 ≤ epsilonCount subset ∧ epsilonCount subset ≤ 1 := by
    unfold epsilonCount
    split_ifs <;> omega
  have etaNonnegative : 0 ≤ (etaCount subset : ℤ) := Int.natCast_nonneg _
  have thetaNonnegative : 0 ≤ (thetaCount subset : ℤ) := Int.natCast_nonneg _
  constructor <;> omega

theorem original_polarized_state_sector (D : LatticeData) (matter : Carrier D)
    (subset : Finset ℕ) :
    LatticeBcGhostBrstGhostNumber.J D (matter ⊗ₜ[ℂ] downWord subset down) =
      ((1 + epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) : ℤ) : ℂ) •
        (matter ⊗ₜ[ℂ] downWord subset down) ∧
    G D 0 (matter ⊗ₜ[ℂ] downWord subset down) =
      ((-1 + polarizedLevel subset : ℤ) : ℂ) • (matter ⊗ₜ[ℂ] downWord subset down) ∧
    B D 0 (matter ⊗ₜ[ℂ] down) = 0 ∧
    B D 0 (matter ⊗ₜ[ℂ] up) = matter ⊗ₜ[ℂ] down ∧
    -polarizedLevel subset ≤
      epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) ∧
    epsilonCount subset + (thetaCount subset : ℤ) - (etaCount subset : ℤ) ≤
      polarizedLevel subset + 1 := by
  obtain ⟨downAction, upAction⟩ := original_b_zero_down_up
  obtain ⟨lower, upper⟩ := ghost_auxiliary_bounds subset
  refine ⟨?_, ?_, ?_, ?_, lower, upper⟩
  · simp [LatticeBcGhostBrstGhostNumber.J, polarized_J, TensorProduct.tmul_smul]
  · simp [G, polarized_L_zero, TensorProduct.tmul_smul]
  · simp [B, downAction]
  · simp [B, upAction]

theorem ghost_part_normalK_down (mode : ℤ) (positive : 0 < mode) :
    c (K := ℂ) (-mode) (b mode down) + b (-mode) (c mode down) = 0 := by
  obtain ⟨bZero, cZero⟩ := positive_modes_down mode positive
  rw [bZero, cZero]
  simp

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
