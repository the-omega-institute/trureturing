/- GID: D5/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ReflectionDiagonalCNOTLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reflection-symmetric diagonal unitaries require the registered worst-case CNOT count. -/

import D5.S3.Quantum.Magic.ReflectionDiagonalParityCounting
import D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation

/-! Formal reading of the reflection-symmetric diagonal synthesis lower-bound conjecture. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Matrix
open Real
open D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation (Qubits)

namespace D5.S3.Quantum.Magic.ReflectionDiagonalCNOTLowerBound

abbrev gate (m : ℕ) :=
  {p : Fin m × Fin m // p.1 ≠ p.2} ⊕ (Fin m × ℝ)

private def cnotMatrix {m : ℕ} (t c : Fin m) (_h : t ≠ c) : Matrix (Qubits m) (Qubits m) ℂ :=
  (1 : Matrix (Qubits m) (Qubits m) ℂ).submatrix id
    (fun y => Function.update y t (Bool.xor (y t) (y c)))

private def rzMatrix {m : ℕ} (q : Fin m) (φ : ℝ) : Matrix (Qubits m) (Qubits m) ℂ :=
  Matrix.diagonal (fun x =>
    if x q = false then Complex.exp (((-φ / 2 : ℝ) : ℂ) * Complex.I)
    else Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I))

def gateMatrix {m : ℕ} : gate m → Matrix (Qubits m) (Qubits m) ℂ
  | Sum.inl p => cnotMatrix p.1.1 p.1.2 p.2
  | Sum.inr p => rzMatrix p.1 p.2

def circuitMatrix {m : ℕ} (circuit : List (gate m)) : Matrix (Qubits m) (Qubits m) ℂ :=
  circuit.foldr (fun g acc => gateMatrix g * acc) 1

def cnotCount {m : ℕ} (circuit : List (gate m)) : ℕ :=
  (circuit.filter (fun g => match g with | Sum.inl _ => true | Sum.inr _ => false)).length

private def character {m : ℕ} (v : Qubits m) (f : Qubits m → ℂ) : ℂ :=
  ∏ x : Qubits m, f x ^ (if dotProduct v x then (-1 : ℤ) else 1)

private def evenLabel {m : ℕ} (v : Qubits m) : Prop :=
  (∑ i, v i) = false

private def updateLabels {m : ℕ} (labels : Fin m → Qubits m) (t c : Fin m) :
    Fin m → Qubits m :=
  ReflectionDiagonalParityCounting.update labels (t, c)

private def wireLabels {m : ℕ} (circuit : List (gate m)) : Fin m → Qubits m :=
  circuit.foldl (fun labels g =>
    match g with
    | Sum.inl p => updateLabels labels p.1.1 p.1.2
    | Sum.inr _ => labels) (1 : Matrix (Fin m) (Fin m) Bool)

private def rotationLabelsAux {m : ℕ} : List (gate m) → (Fin m → Qubits m) → Finset (Qubits m)
  | [], _ => ∅
  | g :: circuit, labels =>
      match g with
      | Sum.inl p => rotationLabelsAux circuit (updateLabels labels p.1.1 p.1.2)
      | Sum.inr p => insert (labels p.1) (rotationLabelsAux circuit labels)

private def rotationLabels {m : ℕ} (circuit : List (gate m)) : Finset (Qubits m) :=
  rotationLabelsAux circuit (1 : Matrix (Fin m) (Fin m) Bool)

private def hardTheta {m : ℕ} (x : Qubits m) : ℝ :=
  if (∀ i, x i = false) ∨ (∀ i, x i = true) then Real.pi / 2 else 0

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ θ : Qubits (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit

private lemma hardTheta_reflection (m : ℕ) (x : Qubits m) :
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
        exact Bool.eq_true_of_not_eq_false' (h i)
      · left
        intro i
        exact Bool.eq_false_of_not_eq_true' (h i)
  by_cases hp : p
  · have hq : q := hiff.mp hp
    change (if q then Real.pi / 2 else 0) = if p then Real.pi / 2 else 0
    rw [ite_eq_left hq, ite_eq_left hp]
  · have hq : ¬q := fun hq => hp (hiff.mpr hq)
    change (if q then Real.pi / 2 else 0) = if p then Real.pi / 2 else 0
    rw [ite_eq_right hq, ite_eq_right hp]

private lemma apply_update {m : ℕ} (labels : Fin m → Qubits m) (t c : Fin m)
    (x : Qubits m) :
    Matrix.mulVec (updateLabels labels t c) x =
      Function.update (Matrix.mulVec labels x) t
        ((Matrix.mulVec labels x t) ^^ (Matrix.mulVec labels x c)) := by
  change (Function.update labels t (labels t + labels c)) *ᵥ x =
    Function.update (labels *ᵥ x) t ((labels *ᵥ x) t + (labels *ᵥ x) c)
  funext j
  simpa only [Matrix.updateRow, Matrix.of_apply, Matrix.mulVec, add_dotProduct] using
    congrFun (Matrix.updateRow_mulVec labels t (labels t + labels c) x) j

private lemma toggle_involutive {m : ℕ} (t c : Fin m) (h : t ≠ c) :
    Function.Involutive (fun x : Qubits m => Function.update x t (x t ^^ x c)) := by
  intro x
  funext j
  by_cases hj : j = t
  · subst j
    simp [Function.update_apply, Ne.symm h, Bool.xor_assoc]
  · simp [Function.update_apply, hj]

private lemma labels_update_bijective {m : ℕ} (labels : Fin m → Qubits m)
    (t c : Fin m) (h : t ≠ c) (ha : Function.Bijective (Matrix.mulVec labels)) :
    Function.Bijective (Matrix.mulVec (updateLabels labels t c)) := by
  have heq : Matrix.mulVec (updateLabels labels t c) =
      (fun x : Qubits m => Function.update x t (x t ^^ x c)) ∘ Matrix.mulVec labels := by
    funext x
    exact apply_update labels t c x
  rw [heq]
  exact (toggle_involutive t c h).bijective.comp ha

private lemma cnot_left {m : ℕ} (t c : Fin m) (h : t ≠ c) (a : Matrix (Qubits m) (Qubits m) ℂ)
    (x y : Qubits m) :
    (cnotMatrix t c h * a) x y = a (Function.update x t (x t ^^ x c)) y := by
  classical
  have hi := toggle_involutive t c h
  change (((1 : Matrix (Qubits m) (Qubits m) ℂ).submatrix id hi.toPerm) * a) x y = _
  rw [Matrix.one_submatrix_mul]
  rfl

private def phaseAux {m : ℕ} : List (gate m) → (Fin m → Qubits m) → Qubits m → ℂ
  | [], _, _ => 1
  | Sum.inl p :: gs, labels, x => phaseAux gs (updateLabels labels p.1.1 p.1.2) x
  | Sum.inr p :: gs, labels, x =>
      (if dotProduct (labels p.1) x = false then Complex.exp (((-p.2 / 2 : ℝ) : ℂ) * Complex.I)
       else Complex.exp (((p.2 / 2 : ℝ) : ℂ) * Complex.I)) * phaseAux gs labels x

private lemma phase_ne_zero {m : ℕ} (gs : List (gate m))
    (labels : Fin m → Qubits m) (x : Qubits m) : phaseAux gs labels x ≠ 0 := by
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
    (labels : Fin m → Qubits m) (x y : Qubits m) :
    circuitMatrix gs (Matrix.mulVec labels x) y = phaseAux gs labels x *
      (if Matrix.mulVec (gs.foldl (fun ls g => match g with
        | Sum.inl p => updateLabels ls p.1.1 p.1.2
        | Sum.inr _ => ls) labels) x = y then 1 else 0) := by
  classical
  induction gs generalizing labels with
  | nil =>
    change (if Matrix.mulVec labels x = y then (1 : ℂ) else 0) =
      1 * (if Matrix.mulVec labels x = y then (1 : ℂ) else 0)
    exact (one_mul _).symm
  | cons g gs ih =>
    cases g with
    | inl p =>
      change (cnotMatrix p.1.1 p.1.2 p.2 * circuitMatrix gs : Matrix (Qubits m) (Qubits m) ℂ) (Matrix.mulVec labels x) y = _
      rw [cnot_left, ← apply_update]
      exact ih (updateLabels labels p.1.1 p.1.2)
    | inr p =>
      change (rzMatrix p.1 p.2 * circuitMatrix gs : Matrix (Qubits m) (Qubits m) ℂ) (Matrix.mulVec labels x) y = _
      unfold rzMatrix
      rw [Matrix.diagonal_mul]
      rw [ih]
      simp only [phaseAux.eq_1, phaseAux.eq_2, phaseAux.eq_3,
        List.foldl_cons, mul_assoc, Matrix.mulVec] <;> rfl

private lemma diagonal_forces_identity (m : ℕ) (circuit : List (gate m)) (c : ℂ)
    (θ : Qubits m → ℝ)
    (h : circuitMatrix circuit =
      c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I))) :
    wireLabels circuit = (1 : Matrix (Fin m) (Fin m) Bool) := by
  classical
  have hfix (x : Qubits m) : Matrix.mulVec (wireLabels circuit) x = x := by
    have heval := matrix_normal circuit (1 : Matrix (Fin m) (Fin m) Bool) x
      (Matrix.mulVec (wireLabels circuit) x)
    rw [Matrix.one_mulVec] at heval
    change circuitMatrix circuit x (Matrix.mulVec (wireLabels circuit) x) =
      phaseAux circuit (1 : Matrix (Fin m) (Fin m) Bool) x *
        (if Matrix.mulVec (wireLabels circuit) x = Matrix.mulVec (wireLabels circuit) x
          then 1 else 0) at heval
    rw [ite_eq_left rfl, mul_one] at heval
    by_contra hn
    have hz : circuitMatrix circuit x (Matrix.mulVec (wireLabels circuit) x) = 0 := by
      rw [h]
      simp [Matrix.smul_apply, Matrix.diagonal_apply, Ne.symm hn]
    exact phase_ne_zero circuit (1 : Matrix (Fin m) (Fin m) Bool) x (heval.symm.trans hz)
  exact Matrix.ext_iff_mulVec.mpr fun x => (hfix x).trans (Matrix.one_mulVec x).symm

private lemma character_mul (m : ℕ) (v : Qubits m) (f g : Qubits m → ℂ) :
    character v (fun x => f x * g x) = character v f * character v g := by
  classical
  simp only [character.eq_1, mul_zpow, Finset.prod_mul_distrib]

private lemma exists_dot_true {m : ℕ} (v : Qubits m) (hv : v ≠ 0) :
    ∃ i, v i = true := by
  simpa only [Pi.zero_apply, Bool.zero_eq_false, Bool.not_eq_false] using Function.ne_iff.mp hv

private lemma character_cancel {m : ℕ} (v u : Qubits m) (f : Qubits m → ℂ)
    (hu : dotProduct v u = true) (hf : ∀ x, f x ≠ 0)
    (hfu : ∀ x, f (x + u) = f x) : character v f = 1 := by
  classical
  unfold character
  apply Finset.prod_ninvolution (fun x => x + u)
  · intro x
    rw [hfu, dotProduct_add, hu]
    cases hx : dotProduct v x <;> simp [hx, Bool.add_eq_xor, hf x]
  · intro x _ h
    have hd := congrArg (dotProduct v) h
    rw [dotProduct_add, hu] at hd
    cases hx : dotProduct v x <;> simp_all [Bool.add_eq_xor]
  · intro x
    exact Finset.mem_univ _
  · intro x
    funext i
    change (x i + u i) + u i = x i
    simp only [Bool.add_eq_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

private lemma character_global (m : ℕ) (v : Qubits m)
    (hv : v ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    character v (fun _ : Qubits m => c) = 1 := by
  obtain ⟨i, hi⟩ := exists_dot_true v hv
  exact character_cancel v ((Pi.single i (1 : Bool))) (fun _ => c)
    (by simpa only [dotProduct_single_one] using hi) (fun _ => hc) (fun _ => rfl)

private lemma character_factor (m : ℕ) (v w : Qubits m) (f : Bool → ℂ)
    (hv : v ≠ 0) (hvw : v ≠ w)
    (hw : w ≠ fun _ : Fin m => false) (hf : ∀ b, f b ≠ 0) :
    character v (fun x => f (dotProduct w x)) = 1 := by
  classical
  obtain ⟨j, hj⟩ := exists_dot_true w hw
  have hsep : ∃ u : Qubits m, dotProduct v u = true ∧ dotProduct w u = false := by
    cases hvj : v j with
    | false =>
      obtain ⟨i, hi⟩ := exists_dot_true v hv
      cases hwi : w i with
      | false => exact ⟨(Pi.single i (1 : Bool)), (dotProduct_single_one v i).trans hi,
          (dotProduct_single_one w i).trans hwi⟩
      | true =>
        refine ⟨(Pi.single i (1 : Bool)) + (Pi.single j (1 : Bool)), ?_, ?_⟩
        · rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, hi, hvj]
          rfl
        · rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, hwi, hj]
          rfl
    | true =>
      have hdiff : ∃ i, v i ≠ w i := Function.ne_iff.mp hvw
      obtain ⟨i, hi⟩ := hdiff
      cases hvi : v i <;> cases hwi : w i
      · exact (hi (hvi.trans hwi.symm)).elim
      · refine ⟨(Pi.single j (1 : Bool)) + (Pi.single i (1 : Bool)), ?_, ?_⟩
        · rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, hvj, hvi]
          rfl
        · rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one, hj, hwi]
          rfl
      · exact ⟨(Pi.single i (1 : Bool)), (dotProduct_single_one v i).trans hvi,
          (dotProduct_single_one w i).trans hwi⟩
      · exact (hi (hvi.trans hwi.symm)).elim
  obtain ⟨u, hvu, hwu⟩ := hsep
  apply character_cancel v u _ hvu (fun x => hf (dotProduct w x))
  intro x
  rw [dotProduct_add, hwu, ← Bool.zero_eq_false, add_zero]

private lemma phase_character {m : ℕ} (gs : List (gate m))
    (labels : Fin m → Qubits m) (v : Qubits m)
    (ha : Function.Bijective (Matrix.mulVec labels)) (hv : v ≠ 0)
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
      have hw : labels p.1 ≠ 0 := by
        intro hz
        obtain ⟨x, hx⟩ := ha.2 (fun _ => true)
        have hh := congrFun hx p.1
        simp only [Matrix.mulVec, hz, zero_dotProduct] at hh
        exact Bool.false_ne_true hh
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
      change character v (fun x => f (dotProduct (labels p.1) x) * phaseAux gs labels x) = 1
      rw [character_mul m v _ _,
        character_factor m v (labels p.1) f hv hvw hw hf, ih labels ha htail, mul_one]

private lemma hard_character (m : ℕ) (hm : 0 < m) (v : Qubits m) (he : evenLabel v) :
    character v (fun x => Complex.exp ((hardTheta x : ℂ) * Complex.I)) = -1 := by
  classical
  let z : Qubits m := 0
  let o : Qubits m := fun _ => true
  let f : Qubits m → ℂ := fun x =>
    Complex.exp ((hardTheta x : ℂ) * Complex.I) ^ (if dotProduct v x then (-1 : ℤ) else 1)
  have hzo : z ≠ o := fun h => Bool.false_ne_true (congrFun h ⟨0, hm⟩)
  have hzθ : hardTheta z = Real.pi / 2 := by
    change (if (∀ i, z i = false) ∨ (∀ i, z i = true) then Real.pi / 2 else 0) = _
    rw [ite_eq_left (Or.inl (by intro i; simp [z, Pi.zero_apply, Bool.zero_eq_false]))]
  have hoθ : hardTheta o = Real.pi / 2 := by
    change (if (∀ i, o i = false) ∨ (∀ i, o i = true) then Real.pi / 2 else 0) = _
    rw [ite_eq_left (Or.inr (by intro i; simp [o]))]
  have hzdot : dotProduct v z = false := dotProduct_zero v
  have hodot : dotProduct v o = false := (dotProduct_one v).trans he
  have hfz : f z = Complex.I := by simp [f, hzdot, hzθ]
  have hfo : f o = Complex.I := by simp [f, hodot, hoθ]
  have hrest (x : Qubits m) (hx : x ∈ (Finset.univ \ {z}) \ {o}) : f x = 1 := by
    have hxz : x ≠ z := by
      intro h
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 (by simpa [h])
    have hxo : x ≠ o := by
      intro h
      exact (Finset.mem_sdiff.mp hx).2 (by simpa [h])
    have hxzero : ¬∀ i, x i = false := fun hzero => hxz (funext hzero)
    have hxone : ¬∀ i, x i = true := fun hone => hxo (funext hone)
    simp [f, hardTheta.eq_1, Pi.zero_apply, hxzero, hxone]
  change ∏ x : Qubits m, f x = -1
  rw [Finset.prod_eq_mul_prod_sdiff_singleton z f (by simp)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton o f (by simp [Ne.symm hzo])]
  have hprod : ∏ x ∈ ((Finset.univ \ {z}) \ {o}), f x = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    exact hrest x hx
  rw [hprod, hfz, hfo]
  simp [Complex.I_mul_I]

private lemma rotation_labels (m : ℕ) (circuit : List (gate m))
    (θ : Qubits m → ℝ) (c : ℂ)
    (h : circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)))
    (hnf : wireLabels circuit = (1 : Matrix (Fin m) (Fin m) Bool))
    (hglobal : ∀ (v : Qubits m) (c : ℂ), v ≠ 0 → c ≠ 0 →
      character v (fun _ : Qubits m => c) = 1)
    (hchars : ∀ v, evenLabel v → v ≠ 0 →
      character v (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) = -1) :
    ∀ v, evenLabel v → v ≠ 0 → v ∈ rotationLabels circuit := by
  classical
  have heval (x : Qubits m) : phaseAux circuit (1 : Matrix (Fin m) (Fin m) Bool) x =
      c * Complex.exp ((θ x : ℂ) * Complex.I) := by
    have hh := matrix_normal circuit (1 : Matrix (Fin m) (Fin m) Bool) x x
    change circuitMatrix circuit (Matrix.mulVec (1 : Matrix (Fin m) (Fin m) Bool) x) x =
      phaseAux circuit (1 : Matrix (Fin m) (Fin m) Bool) x *
        (if Matrix.mulVec (wireLabels circuit) x = x then 1 else 0) at hh
    simp only [hnf, Matrix.one_mulVec, ite_eq_left rfl, mul_one] at hh
    rw [h] at hh
    simpa using hh.symm
  have hc : c ≠ 0 := by
    intro hz
    have hh := heval 0
    rw [hz, zero_mul] at hh
    exact phase_ne_zero circuit (1 : Matrix (Fin m) (Fin m) Bool) 0 hh
  have hi : Function.Bijective (Matrix.mulVec (1 : Matrix (Fin m) (Fin m) Bool)) := by
    simpa only [show Matrix.mulVec (1 : Matrix (Fin m) (Fin m) Bool) = id from
      funext Matrix.one_mulVec] using Function.bijective_id
  intro v he hv
  by_contra hmiss
  have hp := phase_character circuit (1 : Matrix (Fin m) (Fin m) Bool) v hi hv hmiss
  have hh := congrArg (character v) (funext heval)
  rw [character_mul m v _ _,
    hglobal v c hv hc, hchars v he hv, one_mul, hp] at hh
  norm_num at hh

private def cnotPairs {m : ℕ} (gs : List (gate m)) : List (Fin m × Fin m) :=
  gs.filterMap (fun g => match g with | Sum.inl p => some p.1 | Sum.inr _ => none)

private lemma pairs_labels {m : ℕ} (gs : List (gate m)) (ls : Fin m → Qubits m) :
    ReflectionDiagonalParityCounting.labels (cnotPairs gs) ls =
      gs.foldl (fun labels g => match g with
        | Sum.inl p => updateLabels labels p.1.1 p.1.2
        | Sum.inr _ => labels) ls := by
  unfold ReflectionDiagonalParityCounting.labels cnotPairs
  rw [List.foldl_filterMap]
  congr 1
  funext labels g
  cases g <;> rfl

private lemma pairs_count {m : ℕ} (gs : List (gate m)) :
    (cnotPairs gs).length = cnotCount gs := by
  unfold cnotPairs cnotCount
  rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro g _
  cases g <;> rfl

private lemma rotation_outputs {m : ℕ} (gs : List (gate m))
    (ls : Fin m → Qubits m) (v : Qubits m) (hv : v ∈ rotationLabelsAux gs ls) :
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
          simp only [updateLabels.eq_1, ReflectionDiagonalParityCounting.update, Function.update_self, Pi.add_apply, Bool.add_eq_xor]
        · left
          exact ⟨j, by simpa [updateLabels.eq_1, ReflectionDiagonalParityCounting.update, Function.update_apply, hjt] using hj⟩
      · right
        exact List.mem_cons_of_mem _ hh
    | inr p =>
      rw [rotationLabelsAux.eq_def] at hv
      rcases Finset.mem_insert.mp hv with hh | hh
      · exact Or.inl ⟨p.1, hh.symm⟩
      · exact ih ls hh

private lemma initial_odd {m : ℕ} (j : Fin m) :
    (∑ i, (1 : Matrix (Fin m) (Fin m) Bool) j i) = true := by
  simpa only [Matrix.mulVec, dotProduct_one, Pi.one_apply, Bool.one_eq_true] using
    congrFun (Matrix.one_mulVec (1 : Fin m → Bool)) j

private lemma return_count (m : ℕ) (hm : 0 < m) (circuit : List (gate m))
    (hnf : wireLabels circuit = (1 : Matrix (Fin m) (Fin m) Bool))
    (hlabels : ∀ v, evenLabel v → v ≠ 0 → v ∈ rotationLabels circuit) :
    2 ^ (m - 1) + m - 2 ≤ cnotCount circuit := by
  have hs (v : Qubits m) (he : (∑ i, v i) = false) (hv : v ≠ 0) :
      v ∈ ReflectionDiagonalParityCounting.outputs (cnotPairs circuit) (1 : Matrix (Fin m) (Fin m) Bool) := by
    have hr := rotation_outputs circuit (1 : Matrix (Fin m) (Fin m) Bool) v (hlabels v he hv)
    rcases hr with ⟨j, hj⟩ | hr
    · have hh := initial_odd j
      rw [hj, he] at hh
      exact Bool.noConfusion hh
    · exact hr
  have hf (j : Fin m) :
      (∑ i, ReflectionDiagonalParityCounting.labels
        (cnotPairs circuit) (1 : Matrix (Fin m) (Fin m) Bool) j i) = true := by
    rw [pairs_labels]
    change (∑ i, wireLabels circuit j i) = true
    rw [hnf]
    exact initial_odd j
  have hb := ReflectionDiagonalParityCounting.count_bound hm (cnotPairs circuit)
    (1 : Matrix (Fin m) (Fin m) Bool) initial_odd hf hs
  rwa [pairs_count] at hb

private lemma claim_for_n (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : Qubits (2 * n) → ℝ,
      (∀ x, θ (fun j => !(x j)) = θ x) ∧
      ∀ (circuit : List (gate (2 * n))) (c : ℂ),
        circuitMatrix circuit = c • Matrix.diagonal (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) →
          2 ^ (2 * n - 1) + 2 * n - 2 ≤ cnotCount circuit := by
  refine ⟨hardTheta, hardTheta_reflection (2 * n), ?_⟩
  intro circuit c h
  have hidentity := diagonal_forces_identity (2 * n) circuit c hardTheta h
  have hglobal : ∀ (v : Qubits (2 * n)) (d : ℂ), v ≠ 0 → d ≠ 0 →
      character v (fun _ : Qubits (2 * n) => d) = 1 := by
    intro v d hv hd
    exact character_global (2 * n) v hv d hd
  have hchars : ∀ v : Qubits (2 * n), evenLabel v → v ≠ 0 →
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
