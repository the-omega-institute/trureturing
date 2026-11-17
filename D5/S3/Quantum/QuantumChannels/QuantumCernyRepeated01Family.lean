/- GID: D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated 01 words cannot uniquely synchronize a qubit: a rank obstruction yields a shorter synchronizing word. -/

/-
proof_shape: repeated01: definition (parameterized binary word family)
proof_shape: mortal_repeated01: content (dimension-three rank obstruction)
proof_shape: no_qubit_instance_repeated01: content (channel-family obstruction)
admission_basis: escape-witness (mortal_repeated01, consumed by no_qubit_instance_repeated01)
-/

import D5.S3.Quantum.QuantumChannels.QuantumCernyThueMorseRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.QuantumCernyRepeated01Family

open D5.S3.Quantum.QuantumChannels.QuantumCernyThueMorseRefutation
open D5.S3.Quantum.Foundation.FiniteStateChannel Module
open scoped CStarAlgebra ComplexOrder MatrixOrder

/-- Binary words with an initial `01`, a later `01`, and a terminal `1`. -/
def repeated01 (u z : List (Fin 2)) : List (Fin 2) :=
  [0, 1] ++ u ++ [0, 1] ++ z ++ [1]

/-- If a repeated `01` word is mortal in dimension at most three, one of its
shorter structural words is mortal. This is the parameterized rank obstruction
behind the Thue--Morse counterexample below. -/
theorem mortal_repeated01 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : finrank K V ≤ 3) (f : Fin 2 → V →ₗ[K] V)
    (u z : List (Fin 2)) (hw : wordComp f (repeated01 u z) = 0) :
    wordComp f ([0, 1] ++ u ++ [0, 1]) = 0 ∨
      wordComp f ([0, 1] ++ z ++ [1]) = 0 ∨
      wordComp f ([1] ++ u ++ [0, 1] ++ z ++ [1]) = 0 ∨
      wordComp f ([0, 1] ++ u ++ [0, 1] ++ z) = 0 := by
  set f₀ := f 0
  set f₁ := f 1
  have hw' : ∀ x, wordComp f (repeated01 u z) x = 0 :=
    fun x => LinearMap.congr_fun hw x
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hP, hA, hB, hD⟩ := hne
  have ex : ∀ {v : List (Fin 2)}, wordComp f v ≠ 0 → ∃ x, wordComp f v x ≠ 0 := by
    intro v hv
    by_contra h
    push Not at h
    exact hv (LinearMap.ext h)
  obtain ⟨xP, hxP⟩ := ex hP
  obtain ⟨xA, hxA⟩ := ex hA
  obtain ⟨xB, hxB⟩ := ex hB
  obtain ⟨xD, hxD⟩ := ex hD
  let qword : List (Fin 2) := [0, 1]
  let pword : List (Fin 2) := [0, 1] ++ u ++ [0, 1]
  let Q := LinearMap.range (wordComp f qword)
  let P := LinearMap.range (wordComp f pword)
  have append_comp : ∀ (a b : List (Fin 2)),
      wordComp f (a ++ b) = wordComp f b ∘ₗ wordComp f a := by
    intro a
    induction a with
    | nil => intro b; simp [wordComp]
    | cons c a ih =>
      intro b
      simp only [List.cons_append, wordComp, ih, LinearMap.comp_assoc]
  have hfactorP : wordComp f pword =
      wordComp f qword ∘ₗ wordComp f ([0, 1] ++ u) := by
    rw [show pword = ([0, 1] ++ u) ++ [0, 1] by simp [pword, List.append_assoc],
      append_comp]
  have hfullP : wordComp f (repeated01 u z) =
      wordComp f (z ++ [1]) ∘ₗ wordComp f pword := by
    rw [show repeated01 u z = pword ++ (z ++ [1]) by
      simp [repeated01, pword, List.append_assoc], append_comp]
  have hfullQ : wordComp f (repeated01 u z) =
      wordComp f (u ++ [0, 1] ++ z ++ [1]) ∘ₗ wordComp f qword := by
    rw [show repeated01 u z = qword ++ (u ++ [0, 1] ++ z ++ [1]) by
      simp [repeated01, qword, List.append_assoc], append_comp]
  have hfull0 : wordComp f (repeated01 u z) =
      wordComp f ([1] ++ u ++ [0, 1] ++ z ++ [1]) ∘ₗ f₀ := by
    rw [show repeated01 u z = [0] ++ ([1] ++ u ++ [0, 1] ++ z ++ [1]) by
      simp [repeated01, List.append_assoc], append_comp]
    rfl
  have hfull1 : wordComp f (repeated01 u z) =
      f₁ ∘ₗ wordComp f ([0, 1] ++ u ++ [0, 1] ++ z) := by
    rw [show repeated01 u z = ([0, 1] ++ u ++ [0, 1] ++ z) ++ [1] by
      simp [repeated01, List.append_assoc], append_comp]
    rfl
  have hP_le_Q : P ≤ Q := by
    rintro y ⟨x, rfl⟩
    refine ⟨wordComp f ([0, 1] ++ u) x, ?_⟩
    rw [hfactorP]
    rfl
  have hP_pos : 0 < finrank K P := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hbot : P = ⊥ := Submodule.finrank_eq_zero.mp hzero
    apply hxP
    have hxmem : wordComp f pword xP ∈ P := LinearMap.mem_range_self _ _
    rw [hbot, Submodule.mem_bot] at hxmem
    exact hxmem
  have hPQ : finrank K P < finrank K Q := by
    by_contra h
    have heq : P = Q := Submodule.eq_of_le_of_finrank_le hP_le_Q (not_lt.mp h)
    have hmem : wordComp f qword xA ∈ P := heq ▸ LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hmem
    apply hxA
    have hwx := hw' y
    rw [hfullP] at hwx
    simp only [LinearMap.comp_apply] at hwx
    rw [hy] at hwx
    simpa [qword, List.append_assoc, append_comp, wordComp] using hwx
  have hf₀ : LinearMap.range f₀ ≠ ⊤ := by
    intro htop
    obtain ⟨y, hy⟩ : xB ∈ LinearMap.range f₀ := htop ▸ Submodule.mem_top
    apply hxB
    rw [← hy]
    have hwx := hw' y
    simpa [hfull0, LinearMap.comp_apply] using hwx
  have hrank₀ : finrank K (LinearMap.range f₀) ≤ 2 := by
    have := Submodule.finrank_lt hf₀
    omega
  have hQ_le_0 : finrank K Q ≤ finrank K (LinearMap.range f₀) := by
    change finrank K (LinearMap.range (wordComp f [0, 1])) ≤ _
    rw [show wordComp f [0, 1] = f₁ ∘ₗ f₀ by rfl, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  have hQ_pos : 0 < finrank K Q := lt_of_lt_of_le hP_pos (Nat.le_of_lt hPQ)
  have hQ_eq_two : finrank K Q = 2 := by omega
  have hQ_le_1 : Q ≤ LinearMap.range f₁ := by
    dsimp [Q, qword]
    exact LinearMap.range_comp_le_range _ _
  have hrank₁ : 2 < finrank K (LinearMap.range f₁) := by
    by_contra h
    have heq : Q = LinearMap.range f₁ :=
      Submodule.eq_of_le_of_finrank_le hQ_le_1 (by omega)
    have hmem : f₁ xB ∈ Q := heq ▸ LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hmem
    apply hxB
    have hwx := hw' y
    rw [hfullQ] at hwx
    simp only [LinearMap.comp_apply] at hwx
    rw [hy] at hwx
    simpa [List.append_assoc, append_comp, wordComp, LinearMap.comp_apply] using hwx
  have hsurj : Function.Surjective f₁ := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le (LinearMap.range f₁)
    omega
  have hinj : Function.Injective f₁ := LinearMap.injective_iff_surjective.mpr hsurj
  apply hxD
  apply hinj
  rw [map_zero]
  have hwx := hw' xD
  simpa [hfull1, LinearMap.comp_apply] using hwx

/-- A short mortal-word obstruction on spaces of rank at most three rules out
unique shortest synchronization on a qubit. -/
private theorem no_qubit_instance_of_short_mortal (w : List (Fin 2))
    (hobs : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V ≤ 3 → ∀ f : Fin 2 → V →ₗ[ℂ] V, wordComp f w = 0 →
        ∃ v : List (Fin 2), v.length ≤ w.length ∧ v ≠ w ∧ wordComp f v = 0) :
    ¬ HasInstance 2 w := by
  rintro ⟨A, ρ₀, hsync, hshort⟩
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
  have hshort' : ∀ u : List (Fin 2), u.length ≤ w.length → u ≠ w →
      wordComp N u ≠ 0 := fun u hl hne h0 => hshort u hl hne ((hmortal u).mp h0)
  obtain ⟨v, hvlen, hvne, hv0⟩ := hobs (V := V) hV3 N hw
  exact hshort' v hvlen hvne hv0

/-- No pair of qubit channels has a repeated `01` word as its unique shortest
synchronizing word. -/
theorem no_qubit_instance_repeated01 (u z : List (Fin 2)) :
    ¬ HasInstance 2 (repeated01 u z) := by
  apply no_qubit_instance_of_short_mortal
  intro V _ _ _ hV f hw
  have hshort (v : List (Fin 2)) (hv : v.length < (repeated01 u z).length)
      (hzero : wordComp f v = 0) :
      ∃ v' : List (Fin 2), v'.length ≤ (repeated01 u z).length ∧
        v' ≠ repeated01 u z ∧ wordComp f v' = 0 := by
    exact ⟨v, Nat.le_of_lt hv, by intro heq; exact (Nat.ne_of_lt hv) (congrArg List.length heq), hzero⟩
  rcases mortal_repeated01 hV f u z hw with h0 | h0 | h0 | h0
  · exact hshort _ (by simp [repeated01, List.length_append] <;> omega) h0
  · exact hshort _ (by simp [repeated01, List.length_append] <;> omega) h0
  · exact hshort _ (by simp [repeated01, List.length_append] <;> omega) h0
  · exact hshort _ (by simp [repeated01, List.length_append] <;> omega) h0

end D5.S3.Quantum.QuantumChannels.QuantumCernyRepeated01Family
