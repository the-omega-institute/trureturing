/- GID: D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Refutes the conjecture of Lee, Lee and Kjos-Hanssen that the Thue-Morse prefix 01101001 has quantum Cerny complexity 2: no qubit instance has it as unique shortest synchronizing word. -/

/-
proof_shape: applyWord, reachable, Synchronizing, UniqueShortestSync, HasInstance, qc,
  thueMorsePrefix, claim: definition (Definition 1.1 of arXiv:2609.40154 over the frozen
  `QuantumChannel` and `DensityState`, and the conjecture of open problem 1)
proof_shape: wordComp: definition (the composite linear map of a word)
proof_shape: mortal_thueMorse: content (dimension lemma)
proof_shape: result: content
escape_witness: form (1): `mortal_thueMorse`, a new proposition on the live path of `result`:
  for linear maps f₀, f₁ on a space of dimension at most 3, if the word map of 01101001
  vanishes then so does the word map of one of 01101, 01001, 1101001, 0110100. It compares
  the images of the words 01, 01101 and 1 by dimension; `result` applies it to the restriction
  of the two channels to the span of differences of reachable states, which has dimension at
  most 3 for qubits
admission_basis: open-problem-resolution (issue #13185)
Direct frozen dependencies: D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel,
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState and
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.mapState
-/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.QuantumCernyThueMorseRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel Module
open scoped CStarAlgebra ComplexOrder MatrixOrder

/-!
Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen, *Quantum Černý complexity of binary words*,
arXiv:2609.40154 (2026). An instance is a pair of quantum channels `A₀, A₁` on `d × d` density
matrices with a start state `ρ₀`; the letters of a word act left to right, the reachable set is
the set of images of `ρ₀`, a word synchronizes when its channel is constant on the reachable set,
and `qc w` is the least `d ≥ 1` for which some instance has `w` as its unique shortest
synchronizing word. Open problem 1 conjectures `qc(01101001) = 2`.
-/

/-- The channel of a word, letters applied left to right. -/
def applyWord {d : ℕ} (A : Fin 2 → QuantumChannel (Fin d) (Fin d)) :
    List (Fin 2) → DensityState (Fin d) → DensityState (Fin d)
  | [], ρ => ρ
  | a :: u, ρ => applyWord A u ((A a).mapState ρ)

/-- The reachable set `{A_u ρ₀}`. -/
def reachable {d : ℕ} (A : Fin 2 → QuantumChannel (Fin d) (Fin d)) (ρ₀ : DensityState (Fin d)) :
    Set (DensityState (Fin d)) :=
  Set.range fun u => applyWord A u ρ₀

/-- `w` synchronizes the instance: its channel is constant on the reachable set. -/
def Synchronizing {d : ℕ} (A : Fin 2 → QuantumChannel (Fin d) (Fin d))
    (ρ₀ : DensityState (Fin d)) (w : List (Fin 2)) : Prop :=
  ∃ ρ₁ : DensityState (Fin d), ∀ ρ ∈ reachable A ρ₀, applyWord A w ρ = ρ₁

/-- `w` is the unique shortest synchronizing word of the instance. -/
def UniqueShortestSync {d : ℕ} (A : Fin 2 → QuantumChannel (Fin d) (Fin d))
    (ρ₀ : DensityState (Fin d)) (w : List (Fin 2)) : Prop :=
  Synchronizing A ρ₀ w ∧ ∀ u : List (Fin 2), u.length ≤ w.length → u ≠ w → ¬ Synchronizing A ρ₀ u

/-- Some instance of dimension `d` has `w` as its unique shortest synchronizing word. -/
def HasInstance (d : ℕ) (w : List (Fin 2)) : Prop :=
  ∃ (A : Fin 2 → QuantumChannel (Fin d) (Fin d)) (ρ₀ : DensityState (Fin d)),
    UniqueShortestSync A ρ₀ w

/-- The quantum Černý complexity: the least `d ≥ 1` with such an instance. -/
def qc (w : List (Fin 2)) : ℕ :=
  sInf {d | 1 ≤ d ∧ HasInstance d w}

/-- The Thue–Morse prefix `01101001`. -/
def thueMorsePrefix : List (Fin 2) := [0, 1, 1, 0, 1, 0, 0, 1]

/-- Open problem 1 of arXiv:2609.40154: `qc(01101001) = 2`. -/
def claim : Prop := qc thueMorsePrefix = 2

/-- The composite linear map of a word, letters applied left to right. -/
def wordComp {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (f : Fin 2 → V →ₗ[K] V) :
    List (Fin 2) → V →ₗ[K] V
  | [] => LinearMap.id
  | a :: u => wordComp f u ∘ₗ f a

/-- In dimension at most 3, if the word map of `01101001` vanishes then the word map of one of
the shorter words `01101`, `01001`, `1101001`, `0110100` vanishes. -/
theorem mortal_thueMorse {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : finrank K V ≤ 3) (f : Fin 2 → V →ₗ[K] V)
    (hw : wordComp f thueMorsePrefix = 0) :
    wordComp f [0, 1, 1, 0, 1] = 0 ∨ wordComp f [0, 1, 0, 0, 1] = 0 ∨
      wordComp f [1, 1, 0, 1, 0, 0, 1] = 0 ∨ wordComp f [0, 1, 1, 0, 1, 0, 0] = 0 := by
  set f₀ := f 0
  set f₁ := f 1
  have hw' : ∀ x, f₁ (f₀ (f₀ (f₁ (f₀ (f₁ (f₁ (f₀ x))))))) = 0 := fun x => by
    simpa [thueMorsePrefix, wordComp, f₀, f₁] using LinearMap.congr_fun hw x
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hP, hT, hS, hQ⟩ := hne
  have ex : ∀ {u : List (Fin 2)}, wordComp f u ≠ 0 → ∃ x, wordComp f u x ≠ 0 := by
    intro u hu
    by_contra h
    push Not at h
    exact hu (LinearMap.ext h)
  obtain ⟨xP, hxP⟩ := ex hP
  obtain ⟨xT, hxT⟩ := ex hT
  obtain ⟨xS, hxS⟩ := ex hS
  obtain ⟨xQ, hxQ⟩ := ex hQ
  simp only [wordComp, LinearMap.id_comp, LinearMap.comp_apply] at hxP hxT hxS hxQ
  -- `R₂` is the image of the word `01`, `R₅` that of `01101`.
  set R₂ := LinearMap.range (f₁ ∘ₗ f₀) with hR₂
  set R₅ := LinearMap.range (f₁ ∘ₗ f₀ ∘ₗ f₁ ∘ₗ f₁ ∘ₗ f₀) with hR₅
  have h52 : R₅ ≤ R₂ := by
    rintro y ⟨x, rfl⟩
    exact ⟨f₁ (f₁ (f₀ x)), rfl⟩
  have hR₅pos : 0 < finrank K R₅ := by
    apply Nat.pos_of_ne_zero
    intro h
    have hbot : R₅ = ⊥ := Submodule.finrank_eq_zero.mp h
    apply hxP
    have : (f₁ ∘ₗ f₀ ∘ₗ f₁ ∘ₗ f₁ ∘ₗ f₀) xP ∈ R₅ := LinearMap.mem_range_self _ _
    rw [hbot, Submodule.mem_bot] at this
    exact this
  -- Equal images of `01` and `01101` would make `01001` mortal.
  have h25 : finrank K R₅ < finrank K R₂ := by
    by_contra h
    have heq : R₅ = R₂ := Submodule.eq_of_le_of_finrank_le h52 (not_lt.mp h)
    have hmem : (f₁ ∘ₗ f₀) xT ∈ R₅ := heq ▸ LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hmem
    apply hxT
    have := hw' y
    simp only [LinearMap.comp_apply] at hy
    rw [hy] at this
    exact this
  -- `f₀` is not surjective, otherwise `1101001` would be mortal.
  have hf₀ : LinearMap.range f₀ ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy⟩ : xS ∈ LinearMap.range f₀ := htop ▸ Submodule.mem_top
    apply hxS
    rw [← hy]
    exact hw' y
  have hrank₀ : finrank K (LinearMap.range f₀) ≤ 2 := by
    have := Submodule.finrank_lt hf₀
    omega
  have h20 : finrank K R₂ ≤ finrank K (LinearMap.range f₀) := by
    rw [hR₂, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  -- The image of `01` lies in that of `f₁`; equality would make `1101001` mortal.
  have h21 : R₂ ≤ LinearMap.range f₁ := by
    rw [hR₂]
    exact LinearMap.range_comp_le_range _ _
  have hrank₁ : 2 < finrank K (LinearMap.range f₁) := by
    by_contra h
    have heq : R₂ = LinearMap.range f₁ :=
      Submodule.eq_of_le_of_finrank_le h21 (by omega)
    have hmem : f₁ xS ∈ R₂ := heq ▸ LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hmem
    apply hxS
    simp only [LinearMap.comp_apply] at hy
    rw [← hy]
    exact hw' y
  -- Hence `f₁` is surjective, so injective, and `0110100` is mortal.
  have hsurj : Function.Surjective f₁ := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.range f₁)
    omega
  have hinj : Function.Injective f₁ := LinearMap.injective_iff_surjective.mpr hsurj
  apply hxQ
  apply hinj
  rw [map_zero]
  exact hw' xQ

/-- The quantum Černý complexity of `01101001` is not 2: no qubit instance has it as its unique
shortest synchronizing word. -/
theorem result : ¬ claim := by
  intro h
  have hmem : 2 ∈ {d | 1 ≤ d ∧ HasInstance d thueMorsePrefix} := by
    have hne : {d | 1 ≤ d ∧ HasInstance d thueMorsePrefix}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      simp [claim, qc, hemp] at h
    have hin := Nat.sInf_mem hne
    rwa [show sInf {d | 1 ≤ d ∧ HasInstance d thueMorsePrefix} = 2 from h] at hin
  obtain ⟨-, A, ρ₀, hsync, hshort⟩ := hmem
  -- The channels as linear maps on `2 × 2` matrices.
  let L : Fin 2 → CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ :=
    fun a => (A a).toCompletelyPositiveMap.toLinearMap
  have hval : ∀ (u : List (Fin 2)) (ρ : DensityState (Fin 2)),
      (applyWord A u ρ).1 = wordComp L u ρ.1 := by
    intro u
    induction u with
    | nil => intro ρ; rfl
    | cons a u ih =>
      intro ρ
      simp only [applyWord, wordComp, LinearMap.comp_apply, ih]
      rfl
  have happend : ∀ (u v : List (Fin 2)) (ρ : DensityState (Fin 2)),
      applyWord A (u ++ v) ρ = applyWord A v (applyWord A u ρ) := by
    intro u
    induction u with
    | nil => intro v ρ; rfl
    | cons a u ih => intro v ρ; exact ih v _
  -- `V` is the span of differences of reachable states.
  let gen : List (Fin 2) × List (Fin 2) → CStarMatrix (Fin 2) (Fin 2) ℂ :=
    fun p => (applyWord A p.1 ρ₀).1 - (applyWord A p.2 ρ₀).1
  let V : Submodule ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) := Submodule.span ℂ (Set.range gen)
  have hsyncV : ∀ u : List (Fin 2), Synchronizing A ρ₀ u ↔ ∀ x ∈ V, wordComp L u x = 0 := by
    intro u
    constructor
    · rintro ⟨ρ₁, hρ₁⟩ x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, rfl⟩ := hy
        have h₁ := hρ₁ _ ⟨p.1, rfl⟩
        have h₂ := hρ₁ _ ⟨p.2, rfl⟩
        simp only [gen, map_sub, ← hval, h₁, h₂, sub_self]
      | zero => exact map_zero _
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, hy, smul_zero]
    · intro hV
      refine ⟨applyWord A u ρ₀, ?_⟩
      rintro ρ ⟨v, rfl⟩
      apply Subtype.ext
      have := hV (gen (v, [])) (Submodule.subset_span ⟨(v, []), rfl⟩)
      simp only [gen, map_sub, sub_eq_zero] at this
      calc (applyWord A u (applyWord A v ρ₀)).1 = wordComp L u (applyWord A v ρ₀).1 := hval _ _
        _ = wordComp L u (applyWord A [] ρ₀).1 := this
        _ = (applyWord A u ρ₀).1 := (hval _ _).symm
  have hinv : ∀ (a : Fin 2), ∀ x ∈ V, L a x ∈ V := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨(p.1 ++ [a], p.2 ++ [a]), ?_⟩
      simp only [gen, happend]
      rw [hval [a] (applyWord A p.1 ρ₀), hval [a] (applyWord A p.2 ρ₀)]
      simp [wordComp]
    | zero => rw [map_zero]; exact V.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact V.add_mem hy hz
    | smul c y _ hy => rw [map_smul]; exact V.smul_mem c hy
  -- `V` consists of traceless matrices, so it lies in a span of three matrices.
  let e : Fin 3 → CStarMatrix (Fin 2) (Fin 2) ℂ := ![CStarMatrix.ofMatrix !![0, 1; 0, 0],
    CStarMatrix.ofMatrix !![0, 0; 1, 0], CStarMatrix.ofMatrix !![1, 0; 0, -1]]
  have hVe : V ≤ Submodule.span ℂ (Set.range e) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    have t₁ : (applyWord A p.1 ρ₀).1 0 0 + (applyWord A p.1 ρ₀).1 1 1 = 1 := by
      simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using (applyWord A p.1 ρ₀).2.2
    have t₂ : (applyWord A p.2 ρ₀).1 0 0 + (applyWord A p.2 ρ₀).1 1 1 = 1 := by
      simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using (applyWord A p.2 ρ₀).2.2
    refine ⟨![gen p 0 1, gen p 1 0, gen p 0 0], ?_⟩
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, e, gen, CStarMatrix.ofMatrix_apply]
    linear_combination t₂ - t₁
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVe
  have hV3 : finrank ℂ V ≤ 3 :=
    (Submodule.finrank_mono hVe).trans ((finrank_range_le_card e).trans (by simp))
  -- Restrict the channels to `V` and apply the dimension lemma.
  let N : Fin 2 → V →ₗ[ℂ] V := fun a => (L a).restrict (hinv a)
  have hN : ∀ (u : List (Fin 2)) (x : V), (wordComp N u x : CStarMatrix (Fin 2) (Fin 2) ℂ) =
      wordComp L u x := by
    intro u
    induction u with
    | nil => intro x; rfl
    | cons a u ih => intro x; exact ih _
  have hmortal : ∀ u : List (Fin 2), wordComp N u = 0 ↔ Synchronizing A ρ₀ u := by
    intro u
    rw [hsyncV]
    constructor
    · intro h0 x hx
      have := congrArg (fun g => (g ⟨x, hx⟩ : CStarMatrix (Fin 2) (Fin 2) ℂ)) h0
      simpa [hN] using this
    · intro h0
      refine LinearMap.ext fun x => Subtype.ext ?_
      simpa [hN] using h0 x x.2
  have hw := (hmortal _).mpr hsync
  have hshort' : ∀ u : List (Fin 2), u.length ≤ 8 → u ≠ thueMorsePrefix →
      wordComp N u ≠ 0 := fun u hl hne h0 => hshort u hl hne ((hmortal u).mp h0)
  rcases mortal_thueMorse hV3 N hw with h0 | h0 | h0 | h0
  · exact hshort' _ (by decide) (by decide) h0
  · exact hshort' _ (by decide) (by decide) h0
  · exact hshort' _ (by decide) (by decide) h0
  · exact hshort' _ (by decide) (by decide) h0

end D5.S3.Quantum.QuantumChannels.QuantumCernyThueMorseRefutation
