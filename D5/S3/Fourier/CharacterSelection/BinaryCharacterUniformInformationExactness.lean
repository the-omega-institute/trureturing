/- GID: D5/S3/Fourier/CharacterSelection/BinaryCharacterUniformInformationExactness
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/BinaryCharacterUniformInformationExactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform profiles have rank-bit entropy and exact residuals, including degeneracies. -/

/- Library-search audit trail (2026-08-25):
   * Object-name searches covered `profileHom`, binary-character rank, profile entropy, and
     conditional profile entropy. They found no named profile, span, or rank definition, so the
     three source concepts are exported below rather than left inside theorem signatures.
   * Mathlib-name searches covered `PMF.uniformOfFintype`, `PMF.map`, Shannon entropy,
     `Real.negMulLog`, `Real.log_pow`, equal fibers, and finite pushforwards. Mathlib provides
     uniform PMFs and the scalar entropy atom, but no finite Shannon-sum theorem used here.
   * Digest searches for rank bits, uniform input, exact information, and residual entropy found
     `BinaryCharacterSemanticRedundancy`; its public statement has cardinalities, not entropy.
   * Nearby D5 hits are `entropy_eq_log_card_iff_uniform`,
     `quotient_fiber_entropy_decomposition`, and `binary_character_rank_and_redundancy`.
     They are applied below rather than restated.
   * Generalized searches for uniform pushforwards, regular fibers, quotient entropy, and
     deterministic readout decomposition found no public equal-fiber uniform-output theorem.
   * Vocabulary swaps included image/range, profile/syndrome, fiber/kernel coset,
     equivocation/residual entropy, role/character, and rank/dimension.
   * LeanSearch API queries for uniform finite entropy and equal-fiber pushforwards returned no
     response. Loogle type queries for a mapped uniform PMF and log-cardinality returned no hits.
-/

import D5.S3.Entropy.EntropyEquality
import D5.S3.Entropy.Fusion.QuotientFiberDecomposition
import D5.S3.Fourier.CharacterSelection.BinaryCharacterRankAndRedundancy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.BinaryCharacterUniformInformationExactness

open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.EntropyEquality
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Fusion.QuotientFiberDecomposition
open D5.S3.Entropy.MaxEntropy
open D5.S3.Fourier.CharacterSelection.BinaryCharacterRankAndRedundancy

/-- The joint additive profile formed by evaluating every binary character on a group element. -/
def binaryCharacterProfileHom
    {G I : Type*} [AddCommGroup G]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) :
    AddMonoidHom G (I -> ZMod 2) :=
  AddMonoidHom.pi fun i =>
    characters i |>.toAddMonoidHom.comp (ModN.mkQ 2)

/-- The binary-linear span of a family of characters. -/
def binaryCharacterSpan
    {G I : Type*} [AddCommGroup G]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) (ModN G 2)) :=
  Submodule.span (ZMod 2) (Set.range characters)

/-- The finite dimension of the binary-character span. -/
noncomputable def binaryCharacterRank
    {G I : Type*} [AddCommGroup G]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) : Nat :=
  Module.finrank (ZMod 2) (binaryCharacterSpan characters)

private theorem pushforward_uniform_to_range
    {G A : Type*} [AddGroup G] [Fintype G] [AddGroup A] [DecidableEq A]
    (f : AddMonoidHom G A) :
    pushforward (fun g => (⟨f g, ⟨g, rfl⟩⟩ : f.range))
        (fun _ => (Fintype.card G : ℝ)⁻¹) =
      fun _ => (Fintype.card f.range : ℝ)⁻¹ := by
  classical
  funext b
  rw [pushforward]
  simp only [Subtype.ext_iff]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
  have fiberCard :
      Fintype.card {g : G // f g = b.1} = Fintype.card f.ker := by
    rw [Fintype.card_subtype]
    have equalFiber := AddMonoidHom.card_fiber_eq_of_mem_range f
      b.property ⟨0, f.map_zero⟩
    rw [equalFiber]
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr
      (Equiv.subtypeEquivProp (by ext g; simp))
  rw [fiberCard]
  have cardProduct :
      Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using
      (show Nat.card f.ker * Nat.card f.range = Nat.card G by
        rw [← f.ker.card_mul_index, AddSubgroup.index_ker])
  have cardProductReal :
      (Fintype.card G : ℝ) =
        (Fintype.card f.ker : ℝ) * (Fintype.card f.range : ℝ) := by
    exact_mod_cast cardProduct.symm
  rw [cardProductReal]
  have kernelCardNonzero : (Fintype.card f.ker : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card f.ker).ne'
  have rangeCardNonzero : (Fintype.card f.range : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card f.range).ne'
  field_simp

private theorem uniform_entropy_bits
    {X : Type*} [Fintype X] [Nonempty X] :
    shannonEntropy (fun _ : X => (Fintype.card X : ℝ)⁻¹) / Real.log 2 =
      Real.logb 2 (Fintype.card X) := by
  have cardPositive : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos
  have uniformLaw :
      (∀ x : X, 0 ≤ (Fintype.card X : ℝ)⁻¹) ∧
        ∑ _x : X, (Fintype.card X : ℝ)⁻¹ = 1 := by
    constructor
    · intro _x
      exact (inv_pos.mpr cardPositive).le
    · simp
  have entropyEqualsLog :
      shannonEntropy (fun _ : X => (Fintype.card X : ℝ)⁻¹) =
        Real.log (Fintype.card X) :=
    (entropy_eq_log_card_iff_uniform _ uniformLaw).2 rfl
  rw [entropyEqualsLog, Real.logb]

/-- A uniform input makes the realized binary-character profile entropy equal its span rank
when entropy is measured in bits. -/
theorem binary_character_uniform_profile_entropy_bits
    {G : Type*} [AddCommGroup G] [Fintype G]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) :
    let profileHom := binaryCharacterProfileHom characters
    shannonEntropy
          (pushforward
            (fun g => (⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 = binaryCharacterRank characters := by
  classical
  dsimp only
  let profileHom := binaryCharacterProfileHom characters
  let r := binaryCharacterRank characters
  have outputUniform := pushforward_uniform_to_range profileHom
  have rangeNonempty : Nonempty profileHom.range :=
    ⟨⟨0, ⟨0, profileHom.map_zero⟩⟩⟩
  letI : Nonempty profileHom.range := rangeNonempty
  have rangeCardPositive : (0 : ℝ) < Fintype.card profileHom.range := by
    exact_mod_cast Fintype.card_pos
  have uniformLaw :
      (∀ b : profileHom.range,
          0 ≤ (Fintype.card profileHom.range : ℝ)⁻¹) ∧
        ∑ _b : profileHom.range,
          (Fintype.card profileHom.range : ℝ)⁻¹ = 1 := by
    constructor
    · intro _b
      exact (inv_pos.mpr rangeCardPositive).le
    · simp
  have entropyEqualsLog :
      shannonEntropy
          (pushforward
            (fun g => (⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) =
        Real.log (Fintype.card profileHom.range) := by
    rw [outputUniform]
    exact (entropy_eq_log_card_iff_uniform _ uniformLaw).2 rfl
  have rangeCardinality : Fintype.card profileHom.range = 2 ^ r :=
    (binary_character_rank_and_redundancy characters).1
  rw [entropyEqualsLog, rangeCardinality, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]
  exact
    (mul_div_cancel_right₀ (r : ℝ) (Real.log_pos (by norm_num)).ne').trans rfl

#print axioms binary_character_uniform_profile_entropy_bits

/-- For the same uniform input, the state entropy left after observing the profile is the
base-two logarithm of the group size minus the character-span rank. -/
theorem binary_character_uniform_conditional_entropy_bits
    {G : Type*} [AddCommGroup G] [Fintype G]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) :
    let profileHom := binaryCharacterProfileHom characters
    conditionalEntropy
          (pushforward
            (fun g =>
              ((⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range), g))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 =
          Real.logb 2 (Fintype.card G) - binaryCharacterRank characters := by
  classical
  dsimp only
  let profileHom := binaryCharacterProfileHom characters
  let r := binaryCharacterRank characters
  let mass : G -> ℝ := fun _ => (Fintype.card G : ℝ)⁻¹
  let rangeMap : G -> profileHom.range := fun g =>
    ⟨profileHom g, ⟨g, rfl⟩⟩
  have cardPositive : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos
  have massLaw : (∀ g, 0 ≤ mass g) ∧ ∑ g, mass g = 1 := by
    constructor
    · intro g
      exact (inv_pos.mpr cardPositive).le
    · simp [mass]
  have decomposition :=
    (quotient_fiber_entropy_decomposition mass rangeMap massLaw.1 massLaw.2).2
  have sourceEntropyBits :
      shannonEntropy mass / Real.log 2 = Real.logb 2 (Fintype.card G) := by
    simpa only [mass] using (uniform_entropy_bits (X := G))
  have profileEntropyBits :
      shannonEntropy (pushforward rangeMap mass) / Real.log 2 = r := by
    simpa only [rangeMap, mass] using
      binary_character_uniform_profile_entropy_bits characters
  have conditionalEqualsDifference :
      conditionalEntropy
          (pushforward (fun g => (rangeMap g, g)) mass) =
        shannonEntropy mass - shannonEntropy (pushforward rangeMap mass) := by
    linarith
  calc
    conditionalEntropy
          (pushforward
            (fun g =>
              ((⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range), g))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 =
        (shannonEntropy mass - shannonEntropy (pushforward rangeMap mass)) /
          Real.log 2 := by
            rw [← conditionalEqualsDifference]
    _ = shannonEntropy mass / Real.log 2 -
        shannonEntropy (pushforward rangeMap mass) / Real.log 2 := by
          exact sub_div _ _ _
    _ = Real.logb 2 (Fintype.card G) - r := by
          rw [sourceEntropyBits, profileEntropyBits]

#print axioms binary_character_uniform_conditional_entropy_bits

/-- An arbitrary all-zero character family has zero profile entropy and leaves all source
entropy in the conditional term. This includes a zero-rank family on a nontrivial group. -/
theorem zero_character_family_information_bits
    {G : Type*} [AddCommGroup G] [Fintype G]
    {I : Type*} [Fintype I] :
    let characters : I -> Module.Dual (ZMod 2) (ModN G 2) := fun _ => 0
    let profileHom := binaryCharacterProfileHom characters
    shannonEntropy
          (pushforward
            (fun g => (⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 = 0 ∧
      conditionalEntropy
          (pushforward
            (fun g =>
              ((⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range), g))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 = Real.logb 2 (Fintype.card G) := by
  classical
  dsimp only
  have spanZero :
      Submodule.span (ZMod 2)
          (Set.range (fun _ : I =>
            (0 : Module.Dual (ZMod 2) (ModN G 2)))) = ⊥ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro character ⟨i, rfl⟩
      exact Submodule.zero_mem _
    · exact bot_le
  have profileEntropy := binary_character_uniform_profile_entropy_bits
    (fun _ : I => (0 : Module.Dual (ZMod 2) (ModN G 2)))
  have conditionalEntropyValue :=
    binary_character_uniform_conditional_entropy_bits
      (fun _ : I => (0 : Module.Dual (ZMod 2) (ModN G 2)))
  dsimp only at profileEntropy conditionalEntropyValue
  rw [binaryCharacterRank, binaryCharacterSpan, spanZero,
    finrank_bot] at profileEntropy conditionalEntropyValue
  exact ⟨by simpa using profileEntropy, by simpa using conditionalEntropyValue⟩

#print axioms zero_character_family_information_bits

/-- With no characters, the profile has zero bits and conditioning on it retains all source
entropy. -/
theorem empty_character_family_information_bits
    {G : Type*} [AddCommGroup G] [Fintype G] :
    let characters : Fin 0 -> Module.Dual (ZMod 2) (ModN G 2) := fun _ => 0
    let profileHom := binaryCharacterProfileHom characters
    shannonEntropy
          (pushforward
            (fun g => (⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 = 0 ∧
      conditionalEntropy
          (pushforward
            (fun g =>
              ((⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range), g))
            (fun _ => (Fintype.card G : ℝ)⁻¹)) /
        Real.log 2 = Real.logb 2 (Fintype.card G) := by
  simpa only using
    (zero_character_family_information_bits (G := G) (I := Fin 0))

#print axioms empty_character_family_information_bits

set_option maxHeartbeats 1000000 in
/-- On the singleton group, every binary character is zero and both information quantities
vanish, for any finite character index type. -/
theorem singleton_group_character_information_bits
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual (ZMod 2) (ModN Unit 2)) :
    let profileHom := binaryCharacterProfileHom characters
    shannonEntropy
          (pushforward
            (fun g => (⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range))
            (fun _ => (Fintype.card Unit : ℝ)⁻¹)) /
        Real.log 2 = 0 ∧
      conditionalEntropy
          (pushforward
            (fun g =>
              ((⟨profileHom g, ⟨g, rfl⟩⟩ : profileHom.range), g))
            (fun _ => (Fintype.card Unit : ℝ)⁻¹)) /
        Real.log 2 = 0 := by
  have charactersZero : characters = fun _ => 0 := by
    funext i
    ext quotientState
    have quotientStateZero : quotientState = 0 := Subsingleton.elim _ _
    rw [quotientStateZero]
    exact (characters i).map_zero
  subst characters
  simpa [Real.logb] using
    (zero_character_family_information_bits (G := Unit) (I := I))

#print axioms singleton_group_character_information_bits

end D5.S3.Fourier.CharacterSelection.BinaryCharacterUniformInformationExactness
