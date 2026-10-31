/- GID: D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reflection-symmetric diagonal unitaries require the registered worst-case CNOT count. -/

import D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
    rw [ite_eq_left hq, ite_eq_left hp]
  · have hq : ¬q := fun hq => hp (hiff.mpr hq)
    change (if q then Real.pi / 2 else 0) = if p then Real.pi / 2 else 0
    rw [ite_eq_right hq, ite_eq_right hp]

private lemma dot_add_right {m : ℕ} (v x y : basis m) :
    dot v (x + y) = dot v x + dot v y := by
  change (∑ i, v i * (x i + y i)) = (∑ i, v i * x i) + ∑ i, v i * y i
  simp only [mul_add, Finset.sum_add_distrib]

private lemma dot_initial {m : ℕ} (v : basis m) (j : Fin m) :
    dot v (initialLabel j) = v j := by
  classical
  change (∑ i, v i * decide (i = j)) = v j
  rw [Finset.sum_eq_single j]
  · simp [Bool.mul_eq_and]
  · intro i _ hij
    simp [hij, Bool.mul_eq_and, Bool.zero_eq_false]
  · simp

private lemma dot_add_left {m : ℕ} (v w x : basis m) :
    dot (v + w) x = dot v x + dot w x := by
  change (∑ i, (v i + w i) * x i) = (∑ i, v i * x i) + ∑ i, w i * x i
  simp only [add_mul, Finset.sum_add_distrib]

private lemma apply_initial {m : ℕ} (x : basis m) :
    applyLabels (initialLabels m) x = x := by
  funext j
  change dot (initialLabel j) x = x j
  have hcomm : dot (initialLabel j) x = dot x (initialLabel j) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    exact Bool.and_comm _ _
  exact hcomm.trans (dot_initial x j)

private lemma apply_update {m : ℕ} (labels : Fin m → basis m) (t c : Fin m)
    (x : basis m) :
    applyLabels (updateLabels labels t c) x =
      Function.update (applyLabels labels x) t
        ((applyLabels labels x t) ^^ (applyLabels labels x c)) := by
  classical
  funext j
  by_cases hj : j = t
  · subst j
    simp only [applyLabels.eq_1, updateLabels.eq_1, Function.update_self]
    change dot (labels t + labels c) x = dot (labels t) x + dot (labels c) x
    exact dot_add_left _ _ _
  · simp [applyLabels.eq_1, updateLabels.eq_1, Function.update_apply, hj]

private lemma toggle_involutive {m : ℕ} (t c : Fin m) (h : t ≠ c) :
    Function.Involutive (fun x : basis m => Function.update x t (x t ^^ x c)) := by
  intro x
  funext j
  by_cases hj : j = t
  · subst j
    simp [Function.update_apply, Ne.symm h, Bool.xor_assoc]
  · simp [Function.update_apply, hj]

private lemma labels_update_bijective {m : ℕ} (labels : Fin m → basis m)
    (t c : Fin m) (h : t ≠ c) (ha : Function.Bijective (applyLabels labels)) :
    Function.Bijective (applyLabels (updateLabels labels t c)) := by
  have heq : applyLabels (updateLabels labels t c) =
      (fun x : basis m => Function.update x t (x t ^^ x c)) ∘ applyLabels labels := by
    funext x
    exact apply_update labels t c x
  rw [heq]
  exact (toggle_involutive t c h).bijective.comp ha

private lemma cnot_left {m : ℕ} (t c : Fin m) (h : t ≠ c) (a : matrix m)
    (x y : basis m) :
    (cnotMatrix t c h * a) x y = a (Function.update x t (x t ^^ x c)) y := by
  classical
  have hi := toggle_involutive t c h
  change (((1 : matrix m).submatrix id hi.toPerm) * a) x y = _
  rw [Matrix.one_submatrix_mul]
  rfl

private def phaseAux {m : ℕ} : List (gate m) → (Fin m → basis m) → basis m → ℂ
  | [], _, _ => 1
  | Sum.inl p :: gs, labels, x => phaseAux gs (updateLabels labels p.1.1 p.1.2) x
  | Sum.inr p :: gs, labels, x =>
      (if dot (labels p.1) x = false then Complex.exp (((-p.2 / 2 : ℝ) : ℂ) * Complex.I)
       else Complex.exp (((p.2 / 2 : ℝ) : ℂ) * Complex.I)) * phaseAux gs labels x

private lemma phase_ne_zero {m : ℕ} (gs : List (gate m))
    (labels : Fin m → basis m) (x : basis m) : phaseAux gs labels x ≠ 0 := by
  induction gs generalizing labels with
  | nil =>
    rw [phaseAux.eq_def]
    exact one_ne_zero
  | cons g gs ih =>
    cases g with
    | inl p => exact ih _
    | inr p =>
      change (if _ then _ else _) * phaseAux gs labels x ≠ 0
      apply mul_ne_zero _ (ih _)
      split <;> exact Complex.exp_ne_zero _

private lemma matrix_normal {m : ℕ} (gs : List (gate m))
    (labels : Fin m → basis m) (x y : basis m) :
    circuitMatrix gs (applyLabels labels x) y = phaseAux gs labels x *
      (if applyLabels (gs.foldl (fun ls g => match g with
        | Sum.inl p => updateLabels ls p.1.1 p.1.2
        | Sum.inr _ => ls) labels) x = y then 1 else 0) := by
  classical
  induction gs generalizing labels with
  | nil =>
    change (if applyLabels labels x = y then (1 : ℂ) else 0) =
      1 * (if applyLabels labels x = y then (1 : ℂ) else 0)
    exact (one_mul _).symm
  | cons g gs ih =>
    cases g with
    | inl p =>
      change (cnotMatrix p.1.1 p.1.2 p.2 * circuitMatrix gs : matrix m) (applyLabels labels x) y = _
      rw [cnot_left, ← apply_update]
      exact ih (updateLabels labels p.1.1 p.1.2)
    | inr p =>
      change (rzMatrix p.1 p.2 * circuitMatrix gs : matrix m) (applyLabels labels x) y = _
      unfold rzMatrix
      rw [Matrix.diagonal_mul]
      rw [ih]
      simp only [phaseAux.eq_1, phaseAux.eq_2, phaseAux.eq_3,
        List.foldl_cons, mul_assoc, applyLabels.eq_1] <;> rfl

private lemma normal_form (m : ℕ) (circuit : List (gate m)) :
    ∃ a : basis m → basis m, Function.Bijective a ∧
      a = applyLabels (wireLabels circuit) := by
  have hlabels : ∀ (gs : List (gate m)) (labels : Fin m → basis m),
      Function.Bijective (applyLabels labels) →
      Function.Bijective (applyLabels (gs.foldl (fun ls g =>
        match g with
        | Sum.inl p => updateLabels ls p.1.1 p.1.2
        | Sum.inr _ => ls) labels)) := by
    intro gs
    induction gs with
    | nil => intro labels ha; exact ha
    | cons g gs ih =>
      intro labels ha
      cases g with
      | inl p => exact ih _ (labels_update_bijective labels _ _ p.2 ha)
      | inr p => exact ih labels ha
  refine ⟨applyLabels (wireLabels circuit), ?_, rfl⟩
  apply hlabels circuit (initialLabels m)
  have heq : applyLabels (initialLabels m) = id := funext apply_initial
  rw [heq]
  exact Function.bijective_id

private lemma diagonal_forces_identity (m : ℕ) (circuit : List (gate m)) (c : ℂ)
    (θ : basis m → ℝ)
    (h : circuitMatrix circuit =
      c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I))) :
    wireLabels circuit = initialLabels m := by
  classical
  have hfix (x : basis m) : applyLabels (wireLabels circuit) x = x := by
    have heval := matrix_normal circuit (initialLabels m) x
      (applyLabels (wireLabels circuit) x)
    rw [apply_initial] at heval
    change circuitMatrix circuit x (applyLabels (wireLabels circuit) x) =
      phaseAux circuit (initialLabels m) x *
        (if applyLabels (wireLabels circuit) x = applyLabels (wireLabels circuit) x
          then 1 else 0) at heval
    rw [ite_eq_left rfl, mul_one] at heval
    by_contra hn
    have hz : circuitMatrix circuit x (applyLabels (wireLabels circuit) x) = 0 := by
      rw [h]
      simp [Matrix.smul_apply, Matrix.diagonal_apply, Ne.symm hn]
    exact phase_ne_zero circuit (initialLabels m) x (heval.symm.trans hz)
  funext j i
  have hi := congrFun (hfix (initialLabel i)) j
  change dot (wireLabels circuit j) (initialLabel i) = initialLabel i j at hi
  rw [dot_initial] at hi
  simpa [initialLabels.eq_1, initialLabel.eq_1, eq_comm] using hi

private lemma character_mul (m : ℕ) (v : basis m) (f g : basis m → ℂ) :
    character v (fun x => f x * g x) = character v f * character v g := by
  classical
  simp only [character.eq_1, mul_zpow, Finset.prod_mul_distrib]

private lemma exists_dot_true {m : ℕ} (v : basis m) (hv : v ≠ zeroLabel) :
    ∃ i, v i = true := by
  by_contra h
  apply hv
  funext i
  have hi : v i ≠ true := by simpa using fun hi => h ⟨i, hi⟩
  cases hvi : v i <;> simp_all [zeroLabel.eq_1]

private lemma character_cancel {m : ℕ} (v u : basis m) (f : basis m → ℂ)
    (hu : dot v u = true) (hf : ∀ x, f x ≠ 0)
    (hfu : ∀ x, f (x + u) = f x) : character v f = 1 := by
  classical
  unfold character
  apply Finset.prod_ninvolution (fun x => x + u)
  · intro x
    rw [hfu, dot_add_right, hu]
    cases hx : dot v x <;> simp [hx, Bool.add_eq_xor, hf x]
  · intro x _ h
    have hd := congrArg (dot v) h
    rw [dot_add_right, hu] at hd
    cases hx : dot v x <;> simp_all [Bool.add_eq_xor]
  · intro x
    exact Finset.mem_univ _
  · intro x
    funext i
    change (x i + u i) + u i = x i
    cases x i <;> cases u i <;> rfl

private lemma character_global (m : ℕ) (v : basis m)
    (hv : v ≠ zeroLabel) (c : ℂ) (hc : c ≠ 0) :
    character v (fun _ : basis m => c) = 1 := by
  obtain ⟨i, hi⟩ := exists_dot_true v hv
  exact character_cancel v (initialLabel i) (fun _ => c)
    (by simpa only [dot_initial] using hi) (fun _ => hc) (fun _ => rfl)

private lemma character_factor (m : ℕ) (v w : basis m) (f : Bool → ℂ)
    (hv : v ≠ zeroLabel) (hvw : v ≠ w)
    (hw : w ≠ fun _ : Fin m => false) (hf : ∀ b, f b ≠ 0) :
    character v (fun x => f (dot w x)) = 1 := by
  classical
  obtain ⟨j, hj⟩ := exists_dot_true w hw
  have hsep : ∃ u : basis m, dot v u = true ∧ dot w u = false := by
    cases hvj : v j with
    | false =>
      obtain ⟨i, hi⟩ := exists_dot_true v hv
      cases hwi : w i with
      | false => exact ⟨initialLabel i, (dot_initial v i).trans hi,
          (dot_initial w i).trans hwi⟩
      | true =>
        refine ⟨initialLabel i + initialLabel j, ?_, ?_⟩
        · rw [dot_add_right, dot_initial, dot_initial, hi, hvj]
          rfl
        · rw [dot_add_right, dot_initial, dot_initial, hwi, hj]
          rfl
    | true =>
      have hdiff : ∃ i, v i ≠ w i := by
        by_contra hn
        apply hvw
        funext i
        by_contra hi
        exact hn ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hdiff
      cases hvi : v i <;> cases hwi : w i
      · exact (hi (hvi.trans hwi.symm)).elim
      · refine ⟨initialLabel j + initialLabel i, ?_, ?_⟩
        · rw [dot_add_right, dot_initial, dot_initial, hvj, hvi]
          rfl
        · rw [dot_add_right, dot_initial, dot_initial, hj, hwi]
          rfl
      · exact ⟨initialLabel i, (dot_initial v i).trans hvi,
          (dot_initial w i).trans hwi⟩
      · exact (hi (hvi.trans hwi.symm)).elim
  obtain ⟨u, hvu, hwu⟩ := hsep
  apply character_cancel v u _ hvu (fun x => hf (dot w x))
  intro x
  rw [dot_add_right, hwu, ← Bool.zero_eq_false, add_zero]

private lemma phase_character {m : ℕ} (gs : List (gate m))
    (labels : Fin m → basis m) (v : basis m)
    (ha : Function.Bijective (applyLabels labels)) (hv : v ≠ zeroLabel)
    (hmiss : v ∉ rotationLabelsAux gs labels) :
    character v (phaseAux gs labels) = 1 := by
  classical
  induction gs generalizing labels with
  | nil => simp [phaseAux.eq_1, phaseAux.eq_2, phaseAux.eq_3, character.eq_1]
  | cons g gs ih =>
    cases g with
    | inl p =>
      change character v (fun x => phaseAux (Sum.inl p :: gs) labels x) = 1
      simp_rw [phaseAux.eq_2]
      rw [rotationLabelsAux.eq_2] at hmiss
      exact ih _ (labels_update_bijective labels _ _ p.2 ha) hmiss
    | inr p =>
      have hw : labels p.1 ≠ zeroLabel := by
        intro hz
        obtain ⟨x, hx⟩ := ha.2 (fun _ => true)
        have hh := congrFun hx p.1
        simp [applyLabels.eq_1, hz, dot.eq_1, zeroLabel.eq_1, Bool.mul_eq_and] at hh
      have hvw : v ≠ labels p.1 := by
        intro heq
        apply hmiss
        simp [rotationLabelsAux.eq_1, rotationLabelsAux.eq_2, rotationLabelsAux.eq_3, heq]
      have htail : v ∉ rotationLabelsAux gs labels := by
        intro hh
        exact hmiss (Finset.mem_insert_of_mem hh)
      let f : Bool → ℂ := fun b =>
        if b = false then Complex.exp (((-p.2 / 2 : ℝ) : ℂ) * Complex.I)
        else Complex.exp (((p.2 / 2 : ℝ) : ℂ) * Complex.I)
      have hf (b : Bool) : f b ≠ 0 := by
        dsimp [f]
        split <;> exact Complex.exp_ne_zero _
      change character v (fun x => f (dot (labels p.1) x) * phaseAux gs labels x) = 1
      rw [character_mul m v _ _,
        character_factor m v (labels p.1) f hv hvw hw hf, ih labels ha htail, mul_one]

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
    simpa [z, o, zeroLabel.eq_1] using hi
  have hzθ : hardTheta z = Real.pi / 2 := by
    change (if (∀ i, z i = false) ∨ (∀ i, z i = true) then Real.pi / 2 else 0) = _
    rw [ite_eq_left (Or.inl (by intro i; simp [z, zeroLabel.eq_1]))]
  have hoθ : hardTheta o = Real.pi / 2 := by
    change (if (∀ i, o i = false) ∨ (∀ i, o i = true) then Real.pi / 2 else 0) = _
    rw [ite_eq_left (Or.inr (by intro i; simp [o]))]
  have hzdot : dot v z = false := by
    simp [dot.eq_1, z, zeroLabel.eq_1, Bool.mul_eq_and]
  have hodot : dot v o = false := by
    simpa [dot.eq_1, o, evenLabel.eq_1, Bool.mul_eq_and] using he
  have hfz : f z = Complex.I := by simp [f, hzdot, hzθ]
  have hfo : f o = Complex.I := by simp [f, hodot, hoθ]
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
      simp [z, zeroLabel.eq_1, hzero i]
    have hxone : ¬∀ i, x i = true := by
      intro hone
      apply hxo
      funext i
      simp [o, hone i]
    simp [f, hardTheta.eq_1, zeroLabel.eq_1, hxzero, hxone]
  change ∏ x : basis m, f x = -1
  rw [Finset.prod_eq_mul_prod_sdiff_singleton z f (by simp)]
  have hnotmem : o ∉ (Finset.univ : Finset (basis m)) \ {z} → f o = 1 := by
    intro ho
    have hmem : o ∈ ({z} : Finset (basis m)) := by
      by_contra hnmem
      exact ho (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnmem⟩)
    exact (hzo (Finset.mem_singleton.mp hmem).symm).elim
  rw [Finset.prod_eq_mul_prod_sdiff_singleton o f hnotmem]
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
    (hglobal : ∀ (v : basis m) (c : ℂ), v ≠ zeroLabel → c ≠ 0 →
      character v (fun _ : basis m => c) = 1)
    (hchars : ∀ v, evenLabel v → v ≠ zeroLabel →
      character v (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) = -1) :
    ∀ v, evenLabel v → v ≠ zeroLabel → v ∈ rotationLabels circuit := by
  classical
  have heval (x : basis m) : phaseAux circuit (initialLabels m) x =
      c * Complex.exp ((θ x : ℂ) * Complex.I) := by
    have hh := matrix_normal circuit (initialLabels m) x x
    change circuitMatrix circuit (applyLabels (initialLabels m) x) x =
      phaseAux circuit (initialLabels m) x *
        (if applyLabels (wireLabels circuit) x = x then 1 else 0) at hh
    simp only [hnf, apply_initial, ite_eq_left rfl, mul_one] at hh
    rw [h] at hh
    simpa using hh.symm
  have hc : c ≠ 0 := by
    intro hz
    have hh := heval zeroLabel
    rw [hz, zero_mul] at hh
    exact phase_ne_zero circuit (initialLabels m) zeroLabel hh
  have hi : Function.Bijective (applyLabels (initialLabels m)) := by
    obtain ⟨a, ha, heq⟩ := normal_form m []
    simpa [heq, wireLabels.eq_1] using ha
  intro v he hv
  by_contra hmiss
  have hp := phase_character circuit (initialLabels m) v hi hv hmiss
  have hh := congrArg (character v) (funext heval)
  rw [character_mul m v _ _,
    hglobal v c hv hc, hchars v he hv, one_mul, hp] at hh
  norm_num at hh

private def cnotPairs {m : ℕ} (gs : List (gate m)) : List (Fin m × Fin m) :=
  gs.filterMap (fun g => match g with | Sum.inl p => some p.1 | Sum.inr _ => none)

private lemma pairs_labels {m : ℕ} (gs : List (gate m)) (ls : Fin m → basis m) :
    ReflectionDiagonalParityCounting.labels (cnotPairs gs) ls =
      gs.foldl (fun labels g => match g with
        | Sum.inl p => updateLabels labels p.1.1 p.1.2
        | Sum.inr _ => labels) ls := by
  induction gs generalizing ls with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | inl p => exact ih (updateLabels ls p.1.1 p.1.2)
    | inr p => exact ih ls

private lemma pairs_count {m : ℕ} (gs : List (gate m)) :
    (cnotPairs gs).length = cnotCount gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | inl p => simpa [cnotPairs.eq_1, cnotCount.eq_1] using congrArg Nat.succ ih
    | inr p => simpa [cnotPairs.eq_1, cnotCount.eq_1] using ih

private lemma rotation_outputs {m : ℕ} (gs : List (gate m))
    (ls : Fin m → basis m) (v : basis m) (hv : v ∈ rotationLabelsAux gs ls) :
    (∃ j, ls j = v) ∨ v ∈ ReflectionDiagonalParityCounting.outputs (cnotPairs gs) ls := by
  classical
  induction gs generalizing ls with
  | nil => simp [rotationLabelsAux.eq_1, rotationLabelsAux.eq_2, rotationLabelsAux.eq_3] at hv
  | cons g gs ih =>
    cases g with
    | inl p =>
      change (∃ j, ls j = v) ∨
        v ∈ ReflectionDiagonalParityCounting.outputs (p.1 :: cnotPairs gs) ls
      rw [ReflectionDiagonalParityCounting.outputs.eq_2]
      rcases ih (updateLabels ls p.1.1 p.1.2) hv with ⟨j, hj⟩ | hh
      · by_cases hjt : j = p.1.1
        · subst j
          right
          apply List.mem_cons.mpr
          apply Or.inl
          refine hj.symm.trans ?_
          funext i
          simp only [updateLabels.eq_1, Function.update_self, Pi.add_apply, Bool.add_eq_xor]
        · left
          exact ⟨j, by simpa [updateLabels.eq_1, Function.update_apply, hjt] using hj⟩
      · right
        exact List.mem_cons_of_mem _ hh
    | inr p =>
      rw [rotationLabelsAux.eq_def] at hv
      rcases Finset.mem_insert.mp hv with hh | hh
      · exact Or.inl ⟨p.1, hh.symm⟩
      · exact ih ls hh

private lemma initial_odd {m : ℕ} (j : Fin m) :
    (∑ i, initialLabels m j i) = true := by
  simpa [dot.eq_1, initialLabels.eq_1, Bool.mul_eq_and] using dot_initial (fun _ => true) j

private lemma return_count (m : ℕ) (hm : 0 < m) (circuit : List (gate m))
    (hnf : wireLabels circuit = initialLabels m)
    (hlabels : ∀ v, evenLabel v → v ≠ zeroLabel → v ∈ rotationLabels circuit) :
    2 ^ (m - 1) + m - 2 ≤ cnotCount circuit := by
  have hs (v : basis m) (he : (∑ i, v i) = false) (hv : v ≠ 0) :
      v ∈ ReflectionDiagonalParityCounting.outputs (cnotPairs circuit) (initialLabels m) := by
    have hr := rotation_outputs circuit (initialLabels m) v (hlabels v he hv)
    rcases hr with ⟨j, hj⟩ | hr
    · have hh := initial_odd j
      rw [hj, he] at hh
      exact Bool.noConfusion hh
    · exact hr
  have hf (j : Fin m) :
      (∑ i, ReflectionDiagonalParityCounting.labels
        (cnotPairs circuit) (initialLabels m) j i) = true := by
    rw [pairs_labels]
    change (∑ i, wireLabels circuit j i) = true
    rw [hnf]
    exact initial_odd j
  have hb := ReflectionDiagonalParityCounting.count_bound hm (cnotPairs circuit)
    (initialLabels m) initial_odd hf hs
  rwa [pairs_count] at hb

private lemma claim_for_n (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : basis (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit := by
  refine ⟨hardTheta, hardTheta_reflection (2 * n), ?_⟩
  intro circuit c h
  have hidentity := diagonal_forces_identity (2 * n) circuit c hardTheta h
  have hglobal : ∀ (v : basis (2 * n)) (d : ℂ), v ≠ zeroLabel → d ≠ 0 →
      character v (fun _ : basis (2 * n) => d) = 1 := by
    intro v d hv hd
    exact character_global (2 * n) v hv d hd
  have hchars : ∀ v : basis (2 * n), evenLabel v → v ≠ zeroLabel →
      character v (fun x => Complex.exp ((hardTheta x : ℂ) * Complex.I)) = -1 := by
    intro v he _
    exact hard_character (2 * n) (Nat.mul_pos (by decide) hn) v he
  have hlabels := rotation_labels (2 * n) circuit hardTheta c h hidentity
    hglobal hchars
  have hreturn := return_count (2 * n) (Nat.mul_pos (by decide) hn) circuit hidentity hlabels
  exact hreturn

theorem result : claim := by
  intro n hn
  exact claim_for_n n hn

end D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound
