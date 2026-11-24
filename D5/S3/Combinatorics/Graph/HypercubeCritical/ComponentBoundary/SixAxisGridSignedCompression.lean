/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridSignedCompression
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridSignedCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed row cancellation compresses the Huang action to four exterior profiles. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-! Signed sums on the two internal blocks of a normalized six-axis grid. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression

open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang
  (flipSign weightedAction weightedLinear weightedLinear_apply weightedLinear_square)

/-- Join the contiguous blocks A, B and E, in that order. -/
def vertex (a b z : Q 3) : Q 9 := Fin.append a (Fin.append b z)

/-- All-true origin in a block. A false bit denotes a selected axis. -/
def empty : Q 3 := fun _ => true

/-- The block vertex with just axis `i` selected. -/
def single (i : Fin 3) : Q 3 := flip empty i

/-- The four unnormalized sums at a fixed exterior vertex. -/
structure Profiles where
  p : ℤ
  r : ℤ
  q : ℤ
  s : ℤ

/-- Sum the entries with zero or one selected axis in each internal block. -/
def project (f : Q 9 → ℤ) (z : Q 3) : Profiles where
  p := f (vertex empty empty z)
  r := ∑ i, f (vertex (single i) empty z)
  q := ∑ j, f (vertex empty (single j) z)
  s := ∑ i, ∑ j, f (vertex (single i) (single j) z)

/-- The three-axis signed action with the same false-prefix convention. -/
def exteriorAction (f : Q 3 → ℤ) (z : Q 3) : ℤ :=
  ∑ i, flipSign i z * f (flip z i)

theorem flip_append_left {m n : ℕ} (a : Q m) (b : Q n) (i : Fin m) :
    flip (Fin.append a b) (i.castAdd n) = Fin.append (flip a i) b := by
  refine funext (Fin.addCases (fun j => ?_) fun j => ?_)
  · by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip]
    · have h' : j.castAdd n ≠ i.castAdd n := fun e =>
        h (Fin.ext (congrArg (Fin.val : Fin (m + n) → ℕ) e))
      simp [BalancedCriticalSpectrum.flip, Function.update_of_ne h, Function.update_of_ne h']
  · have h : Fin.natAdd m j ≠ i.castAdd n := by
      intro e
      have he := congrArg Fin.val e
      simp only [Fin.val_natAdd, Fin.val_castAdd] at he
      omega
    simp [BalancedCriticalSpectrum.flip, Function.update_of_ne h]

theorem flip_append_right {m n : ℕ} (a : Q m) (b : Q n) (i : Fin n) :
    flip (Fin.append a b) (Fin.natAdd m i) = Fin.append a (flip b i) := by
  refine funext (Fin.addCases (fun j => ?_) fun j => ?_)
  · have h : j.castAdd n ≠ Fin.natAdd m i := by
      intro e
      have he := congrArg Fin.val e
      simp only [Fin.val_natAdd, Fin.val_castAdd] at he
      omega
    simp [BalancedCriticalSpectrum.flip, Function.update_of_ne h]
  · by_cases h : j = i
    · subst j
      simp [BalancedCriticalSpectrum.flip]
    · have h' : Fin.natAdd m j ≠ Fin.natAdd m i := by
        intro e
        apply h
        apply Fin.ext
        have he := congrArg Fin.val e
        simp only [Fin.val_natAdd] at he
        omega
      simp [BalancedCriticalSpectrum.flip, Function.update_of_ne h, Function.update_of_ne h']

private def prefixSign (a : Q 3) : ℤ :=
  (if a 0 then 1 else -1) * ((if a 1 then 1 else -1) * (if a 2 then 1 else -1))

private theorem sign_vertex_a (a b z : Q 3) (i : Fin 3) :
    flipSign (i.castAdd 6) (vertex a b z) = flipSign i a := by
  fin_cases i <;> rfl

private theorem sign_vertex_b (a b z : Q 3) (i : Fin 3) :
    flipSign (Fin.natAdd 3 (i.castAdd 3)) (vertex a b z) =
      prefixSign a * flipSign i b := by
  fin_cases i <;> simp only [prefixSign, mul_assoc] <;> rfl

private theorem sign_vertex_e (a b z : Q 3) (i : Fin 3) :
    flipSign (Fin.natAdd 3 (Fin.natAdd 3 i)) (vertex a b z) =
      (prefixSign a * prefixSign b) * flipSign i z := by
  fin_cases i <;> simp only [prefixSign, mul_assoc] <;> rfl

private theorem row (f : Q 9 → ℤ) (a b z : Q 3) :
    weightedAction (fun _ => (1 : ℤ)) f (vertex a b z) =
      exteriorAction (fun a' => f (vertex a' b z)) a +
      prefixSign a * exteriorAction (fun b' => f (vertex a b' z)) b +
      (prefixSign a * prefixSign b) * exteriorAction (f ∘ vertex a b) z := by
  simp only [weightedAction, Int.cast_id, one_mul, exteriorAction, Function.comp_apply]
  rw [Fin.sum_univ_add (a := 3) (b := 6), Fin.sum_univ_add (a := 3) (b := 3)]
  simp_rw [sign_vertex_a, sign_vertex_b, sign_vertex_e]
  simp only [vertex, flip_append_left, flip_append_right, Finset.mul_sum, mul_assoc]
  abel

private theorem prefixSign_empty : prefixSign empty = 1 := rfl

private theorem prefixSign_single (i : Fin 3) : prefixSign (single i) = -1 := by
  fin_cases i <;> rfl

private theorem exteriorAction_empty (g : Q 3 → ℤ) :
    exteriorAction g empty = ∑ i, g (single i) := by
  apply Finset.sum_congr rfl
  intro i _
  have h : flipSign i empty = 1 := by fin_cases i <;> rfl
  rw [h, one_mul]
  rfl

private theorem sum_exteriorAction_single (g : Q 3 → ℤ) :
    (∑ i, exteriorAction g (single i)) = 3 * g empty := by
  simp only [exteriorAction, Fin.sum_univ_three]
  change (1 * g (flip (single 0) 0) + (-1) * g (flip (single 0) 1) +
      (-1) * g (flip (single 0) 2)) +
    (1 * g (flip (single 1) 0) + 1 * g (flip (single 1) 1) +
      (-1) * g (flip (single 1) 2)) +
    (1 * g (flip (single 2) 0) + 1 * g (flip (single 2) 1) +
      1 * g (flip (single 2) 2)) = _
  -- Swapping the two selected axes pairs the off-diagonal rows with opposite signs.
  rw [show flip (single 1) 0 = flip (single 0) 1 from BalancedCubeGirth.flip_comm _ _ _,
      show flip (single 2) 0 = flip (single 0) 2 from BalancedCubeGirth.flip_comm _ _ _,
      show flip (single 2) 1 = flip (single 1) 2 from BalancedCubeGirth.flip_comm _ _ _]
  simp only [single, BalancedCriticalSpectrum.flip_flip]
  ring

private theorem sum_exteriorAction {ι : Type*} [Fintype ι] (g : ι → Q 3 → ℤ) (z : Q 3) :
    (∑ i, exteriorAction (g i) z) = exteriorAction (fun x => ∑ i, g i x) z := by
  simp only [exteriorAction, Finset.mul_sum]
  exact Finset.sum_comm

/-- The four sums intertwine the actual unit-weight Huang action with the signed exterior action. -/
theorem project_weightedAction (f : Q 9 → ℤ) (z : Q 3) :
    let P := project f
    let HP := project (weightedAction (fun _ => (1 : ℤ)) f) z
    HP.p = (P z).r + (P z).q + exteriorAction (fun x => (P x).p) z ∧
    HP.r = 3 * (P z).p - (P z).s - exteriorAction (fun x => (P x).r) z ∧
    HP.q = 3 * (P z).p + (P z).s - exteriorAction (fun x => (P x).q) z ∧
    HP.s = 3 * (P z).q - 3 * (P z).r + exteriorAction (fun x => (P x).s) z := by
  dsimp only [project]
  simp only [row, prefixSign_empty, prefixSign_single, one_mul, neg_one_mul, mul_one,
    neg_neg, exteriorAction_empty, Function.comp_def, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [sum_exteriorAction_single, sum_exteriorAction]
    ring
  · rw [sum_exteriorAction_single, sum_exteriorAction, Finset.sum_comm (s := Finset.univ)]
    ring
  · simp_rw [sum_exteriorAction_single, sum_exteriorAction, sum_exteriorAction_single,
      ← Finset.mul_sum]
    ring

/-- For an integral three-eigenfunction, the signed exterior action on its mixed sum
vanishes modulo three at every exterior vertex. -/
theorem three_dvd_mixed_of_eigen (f : Q 9 → ℤ)
    (hf : ∀ x, weightedAction (fun _ => (1 : ℤ)) f x = 3 * f x) (z : Q 3) :
    (3 : ℤ) ∣ exteriorAction (fun x => (project f x).s) z := by
  have h := (project_weightedAction f z).2.2.2
  simp only [project, hf, ← Finset.mul_sum] at h
  refine ⟨(project f z).s - (project f z).q + (project f z).r, ?_⟩
  simp only [project]
  linarith

private theorem exteriorAction_square (g : Q 3 → ℤ) (z : Q 3) :
    exteriorAction (exteriorAction g) z = 3 * g z := by
  let w : Fin 9 → ℤ :=
    Fin.append (fun _ : Fin 3 => 0) (Fin.append (fun _ : Fin 3 => 0) (fun _ : Fin 3 => 1))
  have hw : (∑ i, w i ^ 2) = 3 := by decide
  have hW (G : Q 9 → ℤ) (x : Q 3) :
      weightedAction w G (vertex empty empty x) = exteriorAction (G ∘ vertex empty empty) x := by
    simp only [weightedAction, Int.cast_id, exteriorAction, Function.comp_apply]
    rw [Fin.sum_univ_add (a := 3) (b := 6), Fin.sum_univ_add (a := 3) (b := 3)]
    simp_rw [sign_vertex_e]
    simp only [w, Fin.append_left, Fin.append_right, zero_mul, one_mul, Finset.sum_const_zero,
      zero_add, prefixSign_empty, vertex, flip_append_right]
  let lift : Q 9 → ℤ := fun x => g (fun i => x (Fin.natAdd 3 (Fin.natAdd 3 i)))
  have hLift : lift ∘ vertex empty empty = g := by
    funext x
    change g (fun i => vertex empty empty x (Fin.natAdd 3 (Fin.natAdd 3 i))) = g x
    congr 1
    funext i
    simp only [vertex, Fin.append_right]
  have hs := congrArg
    (fun A : Module.End ℤ (Q 9 → ℤ) => A lift (vertex empty empty z))
    (weightedLinear_square w)
  have hrestrict : weightedAction w lift ∘ vertex empty empty = exteriorAction g := by
    funext x
    change weightedAction w lift (vertex empty empty x) = exteriorAction g x
    rw [hW, hLift]
  change weightedLinear w (weightedLinear w lift) (vertex empty empty z) =
    (∑ i, w i ^ 2) * (lift ∘ vertex empty empty) z at hs
  rwa [weightedLinear_apply, weightedLinear_apply, hW, hrestrict, hw, hLift] at hs

private theorem recover_single_profile (u v : Q 3 → ℤ)
    (h : ∀ z, 3 * u z + exteriorAction u z = v z) (z : Q 3) :
    6 * u z = 3 * v z - exteriorAction v z := by
  have hv : exteriorAction v z = 3 * exteriorAction u z + exteriorAction (exteriorAction u) z := by
    calc
      _ = exteriorAction (fun x => 3 * u x + exteriorAction u x) z := by
        exact congrArg (fun g => exteriorAction g z) (funext fun x => (h x).symm)
      _ = _ := by
        change (∑ i, flipSign i z * (3 * u (flip z i) + exteriorAction u (flip z i))) =
          3 * (∑ i, flipSign i z * u (flip z i)) +
            ∑ i, flipSign i z * exteriorAction u (flip z i)
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [exteriorAction_square] at hv
  linarith [h z]

/-- The empty and mixed profiles determine both singleton profiles of a three-eigenfunction. -/
theorem reconstruct_single_profiles_of_eigen (f : Q 9 → ℤ)
    (hf : ∀ x, weightedAction (fun _ => (1 : ℤ)) f x = 3 * f x) (z : Q 3) :
    let P := project f
    let u := fun x => 3 * (P x).p - (P x).s
    let v := fun x => 3 * (P x).p + (P x).s
    6 * (P z).r = 3 * u z - exteriorAction u z ∧
    6 * (P z).q = 3 * v z - exteriorAction v z := by
  refine ⟨recover_single_profile (fun x => (project f x).r)
    (fun x => 3 * (project f x).p - (project f x).s) (fun x => ?_) z,
    recover_single_profile (fun x => (project f x).q)
      (fun x => 3 * (project f x).p + (project f x).s) (fun x => ?_) z⟩
  · have h := (project_weightedAction f x).2.1
    simp only [project, hf, ← Finset.mul_sum] at h
    dsimp only [project]
    linarith
  · have h := (project_weightedAction f x).2.2.1
    simp only [project, hf, ← Finset.mul_sum] at h
    dsimp only [project]
    linarith

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.project_weightedAction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms project_weightedAction
/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.three_dvd_mixed_of_eigen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms three_dvd_mixed_of_eigen
/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression.reconstruct_single_profiles_of_eigen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms reconstruct_single_profiles_of_eigen

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression
