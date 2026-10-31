/- GID: D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reflection-symmetric diagonal unitaries require the registered worst-case CNOT count. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Order

/-! Formal reading of the reflection-symmetric diagonal synthesis lower-bound conjecture. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
open Real

namespace D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound

abbrev basis (m : ℕ) := Fin m → Bool
abbrev matrix (m : ℕ) := Matrix (basis m) (basis m) ℂ

abbrev gate (m : ℕ) :=
  {p : Fin m × Fin m // p.1 ≠ p.2} ⊕ (Fin m × ℝ)

private def cnotMatrix {m : ℕ} (t c : Fin m) (_h : t ≠ c) : matrix m :=
  Matrix.of fun x y => if x = Function.update y t (Bool.xor (y t) (y c)) then 1 else 0

private def rzMatrix {m : ℕ} (q : Fin m) (φ : ℝ) : matrix m :=
  Matrix.diagonal (fun x =>
    if x q = false then Complex.exp (((-φ / 2 : ℝ) : ℂ) * Complex.I)
    else Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I))

def gateMatrix {m : ℕ} : gate m → matrix m
  | Sum.inl p => cnotMatrix p.1.1 p.1.2 p.2
  | Sum.inr p => rzMatrix p.1 p.2

def circuitMatrix {m : ℕ} (circuit : List (gate m)) : matrix m :=
  circuit.foldr (fun g acc => gateMatrix g * acc) 1

def cnotCount {m : ℕ} (circuit : List (gate m)) : ℕ :=
  (circuit.filter (fun g => match g with | Sum.inl _ => true | Sum.inr _ => false)).length

private def dot {m : ℕ} (v x : basis m) : Bool :=
  ∑ i, (v i && x i)

private def character {m : ℕ} (v : basis m) (f : basis m → ℂ) : ℂ :=
  ∏ x : basis m, f x ^ (if dot v x then (-1 : ℤ) else 1)

private def evenLabel {m : ℕ} (v : basis m) : Prop :=
  (∑ i, v i) = false

private def zeroLabel {m : ℕ} : basis m := fun _ => false

private def initialLabel {m : ℕ} (j : Fin m) : basis m := fun i => decide (i = j)

private def initialLabels (m : ℕ) : Fin m → basis m := initialLabel

private def updateLabels {m : ℕ} (labels : Fin m → basis m) (t c : Fin m) :
    Fin m → basis m :=
  Function.update labels t (fun i => Bool.xor (labels t i) (labels c i))

private def wireLabels {m : ℕ} (circuit : List (gate m)) : Fin m → basis m :=
  circuit.foldl (fun labels g =>
    match g with
    | Sum.inl p => updateLabels labels p.1.1 p.1.2
    | Sum.inr _ => labels) (initialLabels m)

private def rotationLabelsAux {m : ℕ} : List (gate m) → (Fin m → basis m) → Finset (basis m)
  | [], _ => ∅
  | g :: circuit, labels =>
      match g with
      | Sum.inl p => rotationLabelsAux circuit (updateLabels labels p.1.1 p.1.2)
      | Sum.inr p => insert (labels p.1) (rotationLabelsAux circuit labels)

private def rotationLabels {m : ℕ} (circuit : List (gate m)) : Finset (basis m) :=
  rotationLabelsAux circuit (initialLabels m)

private def applyLabels {m : ℕ} (labels : Fin m → basis m) (x : basis m) : basis m :=
  fun j => dot (labels j) x

private def hardTheta {m : ℕ} (x : basis m) : ℝ :=
  if (∀ i, x i = false) ∨ (∀ i, x i = true) then Real.pi / 2 else 0

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ θ : basis (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit

private lemma hardTheta_reflection (m : ℕ) (x : basis m) :
    hardTheta (fun j => !(x j)) = hardTheta x := by
  unfold hardTheta
  let p : Prop := (∀ i, x i = false) ∨ (∀ i, x i = true)
  let q : Prop := (∀ i, (!x i) = false) ∨ (∀ i, (!x i) = true)
  have hiff : p ↔ q := by
    constructor
    · intro h
      rcases h with h | h
      · right
        intro i
        simp [h i]
      · left
        intro i
        simp [h i]
    · intro h
      rcases h with h | h
      · right
        intro i
        have hi := h i
        cases hx : x i <;> simp_all
      · left
        intro i
        have hi := h i
        cases hx : x i <;> simp_all
  by_cases hp : p
  · have hq : q := hiff.mp hp
    change (if q then Real.pi / 2 else 0) = if p then Real.pi / 2 else 0
    rw [if_pos hq, if_pos hp]
  · have hq : ¬q := fun hq => hp (hiff.mpr hq)
    change (if q then Real.pi / 2 else 0) = if p then Real.pi / 2 else 0
    rw [if_neg hq, if_neg hp]

private lemma normal_form (m : ℕ) (circuit : List (gate m)) :
    ∃ a : basis m → basis m, Function.Bijective a ∧
      a = applyLabels (wireLabels circuit) := by
  classical
  let toggle : Fin m → Fin m → basis m → basis m := fun t c x =>
    Function.update x t (Bool.xor (x t) (x c))
  have htoggle (t c : Fin m) (h : t ≠ c) :
      Function.Bijective (toggle t c) := by
    have hinv (x : basis m) : toggle t c (toggle t c x) = x := by
      funext j
      by_cases hj : j = t
      · subst j
        have hc : c ≠ t := Ne.symm h
        simp [toggle, Function.update_apply, hc, Bool.xor_assoc,
          Bool.xor_left_comm, Bool.xor_comm]
      · simp [toggle, Function.update_apply, hj]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hxy' := congrArg (toggle t c) hxy
      simpa only [hinv] using hxy'
    · intro y
      exact ⟨toggle t c y, hinv y⟩
  have happly (labels : Fin m → basis m) (t c : Fin m) (h : t ≠ c) :
      applyLabels (updateLabels labels t c) = toggle t c ∘ applyLabels labels := by
    have hsum (a b x : basis m) :
        (∑ i, ((a i ^^ b i) && x i)) =
          ((∑ i, (a i && x i)) ^^ (∑ i, (b i && x i))) := by
      classical
      induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
      | empty => rfl
      | @insert z s hz ih =>
          rw [Finset.sum_insert hz, Finset.sum_insert hz, Finset.sum_insert hz]
          rw [Bool.and_xor_distrib_right, ih]
          simp [Bool.add_eq_xor, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
    funext x j
    by_cases hj : j = t
    · subst j
      simp only [Function.comp_apply, applyLabels, updateLabels, toggle,
        Function.update_apply, dot]
      exact hsum (labels t) (labels c) x
    · simp [applyLabels, updateLabels, toggle, Function.update_apply, hj]
  have hupdate (labels : Fin m → basis m) (t c : Fin m) (h : t ≠ c)
      (ha : Function.Bijective (applyLabels labels)) :
      Function.Bijective (applyLabels (updateLabels labels t c)) := by
    rw [happly labels t c h]
    exact (htoggle t c h).comp ha
  have hlabels : ∀ (gs : List (gate m)) (labels : Fin m → basis m),
      Function.Bijective (applyLabels labels) →
      Function.Bijective (applyLabels (gs.foldl (fun ls g =>
        match g with
        | Sum.inl p => updateLabels ls p.1.1 p.1.2
        | Sum.inr _ => ls) labels)) := by
    intro gs
    induction gs with
    | nil =>
        intro labels ha
        simpa using ha
    | cons g gs ih =>
        intro labels ha
        cases g with
        | inl p =>
            apply ih
            exact hupdate labels p.1.1 p.1.2 p.2 ha
        | inr p =>
            apply ih labels ha
  have hi : Function.Bijective (applyLabels (initialLabels m)) := by
    have hselect (j : Fin m) (y : basis m) :
        (∑ i, (decide (i = j) && y i)) = y j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i hi hij
        have hz : decide (i = j) = false := by simp [hij]
        simp [hz, Bool.mul_eq_and]
        rfl
      · simp
    refine ⟨?_, ?_⟩
    · intro x y hxy
      funext j
      have hj :
          (∑ i, (decide (i = j) && x i)) =
            (∑ i, (decide (i = j) && y i)) := by
        simpa [applyLabels, initialLabels, initialLabel, dot] using congrFun hxy j
      exact (hselect j x).symm.trans (hj.trans (hselect j y))
    · intro y
      refine ⟨y, ?_⟩
      funext j
      exact hselect j y
  refine ⟨applyLabels (wireLabels circuit), ?_, rfl⟩
  exact hlabels circuit (initialLabels m) hi

private lemma diagonal_forces_identity (m : ℕ) (circuit : List (gate m)) (c : ℂ)
    (θ : basis m → ℝ)
    (hnorm : ∃ a : basis m → basis m, Function.Bijective a ∧
      a = applyLabels (wireLabels circuit))
    (h : circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I))) :
    wireLabels circuit = initialLabels m := by sorry

private lemma character_mul (m : ℕ) (v : basis m) (f g : basis m → ℂ)
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) :
    character v (fun x => f x * g x) = character v f * character v g := by
  classical
  simp only [character, mul_zpow, Finset.prod_mul_distrib]

private lemma character_global (m : ℕ) (hm : 0 < m) (v : basis m)
    (hv : v ≠ zeroLabel) (c : ℂ) (hc : c ≠ 0) :
    character v (fun _ : basis m => c) = 1 := by sorry

private lemma character_factor (m : ℕ) (v w : basis m) (f : Bool → ℂ)
    (hv : v ≠ zeroLabel) (hvw : v ≠ w)
    (hw : w ≠ fun _ : Fin m => false) (hf : ∀ b, f b ≠ 0) :
    character v (fun x => f (dot w x)) = 1 := by sorry

private lemma hard_character (m : ℕ) (hm : 0 < m) (v : basis m) (he : evenLabel v) :
    character v (fun x => Complex.exp ((hardTheta x : ℂ) * Complex.I)) = -1 := by
  classical
  let z : basis m := zeroLabel
  let o : basis m := fun _ => true
  let f : basis m → ℂ := fun x =>
    Complex.exp ((hardTheta x : ℂ) * Complex.I) ^ (if dot v x then (-1 : ℤ) else 1)
  have hzo : z ≠ o := by
    intro h
    have hi := congrFun h ⟨0, hm⟩
    simpa [z, o, zeroLabel] using hi
  have hzθ : hardTheta z = Real.pi / 2 := by
    change (if (∀ i, z i = false) ∨ (∀ i, z i = true) then Real.pi / 2 else 0) = _
    rw [if_pos (Or.inl (by intro i; simp [z, zeroLabel]))]
  have hoθ : hardTheta o = Real.pi / 2 := by
    change (if (∀ i, o i = false) ∨ (∀ i, o i = true) then Real.pi / 2 else 0) = _
    rw [if_pos (Or.inr (by intro i; simp [o]))]
  have hzdot : dot v z = false := by
    simp [dot, z, zeroLabel, Bool.mul_eq_and]
  have hodot : dot v o = false := by
    simpa [dot, o, evenLabel, Bool.mul_eq_and] using he
  have hphase : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_ofReal_mul_I, cos_pi_div_two, sin_pi_div_two]
    simp
  have hfz : f z = Complex.I := by simp [f, hzdot, hzθ, hphase]
  have hfo : f o = Complex.I := by simp [f, hodot, hoθ, hphase]
  have hrest (x : basis m) (hx : x ∈ (Finset.univ \ {z}) \ {o}) : f x = 1 := by
    have hxz : x ≠ z := by
      intro h
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 (by simpa [h])
    have hxo : x ≠ o := by
      intro h
      exact (Finset.mem_sdiff.mp hx).2 (by simpa [h])
    have hxzero : ¬∀ i, x i = false := by
      intro hzero
      apply hxz
      funext i
      simp [z, zeroLabel, hzero i]
    have hxone : ¬∀ i, x i = true := by
      intro hone
      apply hxo
      funext i
      simp [o, hone i]
    simp [f, hardTheta, zeroLabel, hxzero, hxone]
  change ∏ x : basis m, f x = -1
  rw [Finset.prod_eq_mul_prod_diff_singleton z f (by simp)]
  have hnotmem : o ∉ (Finset.univ : Finset (basis m)) \ {z} → f o = 1 := by
    intro ho
    have hmem : o ∈ ({z} : Finset (basis m)) := by
      by_contra hnmem
      exact ho (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnmem⟩)
    exact (hzo (Finset.mem_singleton.mp hmem).symm).elim
  rw [Finset.prod_eq_mul_prod_diff_singleton o f hnotmem]
  have hprod : ∏ x ∈ ((Finset.univ \ {z}) \ {o}), f x = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    exact hrest x hx
  rw [hprod, hfz, hfo]
  simp [Complex.I_mul_I]

private lemma rotation_labels (m : ℕ) (circuit : List (gate m))
    (θ : basis m → ℝ) (c : ℂ)
    (h : circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)))
    (hnf : wireLabels circuit = initialLabels m)
    (hmul : ∀ (v : basis m) (f g : basis m → ℂ),
      (∀ x, f x ≠ 0) → (∀ x, g x ≠ 0) →
        character v (fun x => f x * g x) = character v f * character v g)
    (hglobal : ∀ (v : basis m) (c : ℂ), v ≠ zeroLabel → c ≠ 0 →
      character v (fun _ : basis m => c) = 1)
    (hfactor : ∀ (v w : basis m) (f : Bool → ℂ), v ≠ zeroLabel → v ≠ w →
      w ≠ zeroLabel → (∀ b, f b ≠ 0) →
        character v (fun x => f (dot w x)) = 1)
    (hchars : ∀ v, evenLabel v → v ≠ zeroLabel →
      character v (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) = -1) :
    ∀ v, evenLabel v → v ≠ zeroLabel → v ∈ rotationLabels circuit := by sorry

private lemma even_output_count (m : ℕ) (circuit : List (gate m))
    (hnf : wireLabels circuit = initialLabels m)
    (hlabels : ∀ v, evenLabel v → v ≠ zeroLabel → v ∈ rotationLabels circuit) :
    2 ^ (m - 1) - 1 ≤ cnotCount circuit := by sorry

private lemma birth_count (m : ℕ) (circuit : List (gate m))
    (hnf : wireLabels circuit = initialLabels m)
    (hlabels : ∀ v, evenLabel v → v ≠ zeroLabel → v ∈ rotationLabels circuit) :
    m - 1 ≤ cnotCount circuit := by sorry

private lemma return_count (m : ℕ) (circuit : List (gate m))
    (hnf : wireLabels circuit = initialLabels m)
    (hlabels : ∀ v, evenLabel v → v ≠ zeroLabel → v ∈ rotationLabels circuit) :
    2 ^ (m - 1) + m - 2 ≤ cnotCount circuit := by sorry

private lemma claim_for_n (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : basis (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit := by
  refine ⟨hardTheta, hardTheta_reflection (2 * n), ?_⟩
  intro circuit c h
  have hnorm := normal_form (2 * n) circuit
  have hidentity := diagonal_forces_identity (2 * n) circuit c hardTheta hnorm h
  have hmul : ∀ (v : basis (2 * n)) (f g : basis (2 * n) → ℂ),
      (∀ x, f x ≠ 0) → (∀ x, g x ≠ 0) →
        character v (fun x => f x * g x) = character v f * character v g := by
    intro v f g hf hg
    exact character_mul (2 * n) v f g hf hg
  have hglobal : ∀ (v : basis (2 * n)) (d : ℂ), v ≠ zeroLabel → d ≠ 0 →
      character v (fun _ : basis (2 * n) => d) = 1 := by
    intro v d hv hd
    exact character_global (2 * n) (Nat.mul_pos (by decide) hn) v hv d hd
  have hfactor : ∀ (v w : basis (2 * n)) (f : Bool → ℂ), v ≠ zeroLabel → v ≠ w →
      w ≠ zeroLabel → (∀ b, f b ≠ 0) →
        character v (fun x => f (dot w x)) = 1 := by
    intro v w f hv hvw hw hf
    exact character_factor (2 * n) v w f hv hvw hw hf
  have hchars : ∀ v : basis (2 * n), evenLabel v → v ≠ zeroLabel →
      character v (fun x => Complex.exp ((hardTheta x : ℂ) * Complex.I)) = -1 := by
    intro v he _
    exact hard_character (2 * n) (Nat.mul_pos (by decide) hn) v he
  have hlabels := rotation_labels (2 * n) circuit hardTheta c h hidentity
    hmul hglobal hfactor hchars
  have houtputs := even_output_count (2 * n) circuit hidentity hlabels
  have hbirths := birth_count (2 * n) circuit hidentity hlabels
  have hreturn := return_count (2 * n) circuit hidentity hlabels
  exact hreturn

theorem result : claim := by
  intro n hn
  exact claim_for_n n hn

end D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
