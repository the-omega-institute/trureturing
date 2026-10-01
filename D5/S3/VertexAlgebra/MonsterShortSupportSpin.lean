/- GID: D5/S3/VertexAlgebra/MonsterShortSupportSpin
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterShortSupportSpin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Monster labels carry quadratic parity and a public short-support API. -/

/-
proof_shape: finite_quadratic_ground_sections: content
escape_witness: The quadratic label is independent of the section map; right-additivity
  gives its ground value, and the opposite law gives distinct-section polar pairing.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/VertexAlgebra/MonsterShortSupport.unique_short_support.
-/

import D5.S3.VertexAlgebra.MonsterShortSupport
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.VertexAlgebra.MonsterShortSupportSpin

open D5.S3.VertexAlgebra.MonsterCharacterCarry
open D5.S3.VertexAlgebra.MonsterFusionSpan
open D5.S3.VertexAlgebra.MonsterShortSupport

theorem sixMap_explicit (f : E → E → F) (c : Six) :
    sixMap f c =
      c.1 • groundSection f (unit 0) + c.2.1 • groundSection f (unit 1) +
        c.2.2.1 • groundSection f (unit 2) +
          c.2.2.2.1 • groundSection f (unit 0 + unit 1) +
            c.2.2.2.2.1 • groundSection f (unit 0 + unit 2) +
              c.2.2.2.2.2 • groundSection f (unit 1 + unit 2) := by
  change
    c.1 • groundSection f (unit 0) + c.2.1 • groundSection f (unit 1) +
        c.2.2.1 • groundSection f (unit 2) +
          c.2.2.2.1 • groundSection f (unit 0 + unit 1) +
            c.2.2.2.2.1 • groundSection f (unit 0 + unit 2) +
              c.2.2.2.2.2 • groundSection f (unit 1 + unit 2) = _
  rfl

theorem sixMap_allOnes_explicit (f : E → E → F) (hf : IsSignTable f) :
    sixMap f (1, 1, 1, 1, 1, 1) =
      groundSection f (unit 0 + unit 1 + unit 2) := by
  have hrel := (fusion_span_and_capacity f hf).2.1
  have hneg (a : Label) : -a = a := by
    apply Prod.ext <;> funext i <;> exact CharTwo.neg_eq _
  have h := (add_eq_zero_iff_eq_neg.mp hrel).trans (hneg _)
  change
    groundSection f (unit 0) + groundSection f (unit 1) + groundSection f (unit 2) +
        groundSection f (unit 0 + unit 1) + groundSection f (unit 0 + unit 2) +
          groundSection f (unit 1 + unit 2) =
      groundSection f (unit 0 + unit 1 + unit 2) at h
  rw [sixMap_explicit]
  simpa using h

abbrev Coeff := Fin 7 → F

/-- Public support weight for the seven-section coefficient vector. -/
def shortWeight (c : Coeff) : Nat :=
  (Finset.univ.filter (fun i => c i = 1)).card

/-- The finite quadratic parity on a six-bit label `(g, ξ)`. -/
def labelQuadratic (x : Label) : F :=
  x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2

@[simp] theorem labelQuadratic_apply (x : Label) :
    labelQuadratic x = x.1 0 * x.2 0 + x.1 1 * x.2 1 + x.1 2 * x.2 2 := rfl

private theorem coords (g : E) :
    g = g 0 • unit 0 + g 1 • unit 1 + g 2 • unit 2 := by
  funext i
  fin_cases i <;> simp [unit, Pi.add_apply, Pi.smul_apply]

private theorem right_smul (f : E → E → F) (hf : IsSignTable f)
    (g v : E) (a : F) : f g (a • v) = a * f g v := by
  have hcases : ∀ z : F, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hcases := hcases a
  rcases hcases with rfl | rfl
  · rw [zero_smul, hf.zero_right, zero_mul]
  · simp

private theorem eval_coords (f : E → E → F) (hf : IsSignTable f) (g h : E) :
    f g h = h 0 * f g (unit 0) + h 1 * f g (unit 1) + h 2 * f g (unit 2) := by
  have hc := coords h
  calc
    f g h = f g (h 0 • unit 0 + h 1 • unit 1 + h 2 • unit 2) := congrArg (f g) hc
    _ = f g (h 0 • unit 0) + f g (h 1 • unit 1) + f g (h 2 • unit 2) := by
      rw [hf.right_add, hf.right_add]
    _ = h 0 * f g (unit 0) + h 1 * f g (unit 1) + h 2 * f g (unit 2) := by
      rw [right_smul f hf, right_smul f hf, right_smul f hf]

private theorem ground_quadratic_formula (f : E → E → F) (hf : IsSignTable f) (g : E) :
    labelQuadratic (groundSection f g) = f g g := by
  calc
    labelQuadratic (groundSection f g) =
        g 0 * f g (unit 0) + g 1 * f g (unit 1) + g 2 * f g (unit 2) := by
      simp [labelQuadratic, groundSection, ell]
    _ = f g g := (eval_coords f hf g g).symm

/-- The quadratic parity of a ground section is its diagonal sign. -/
theorem labelQuadratic_groundSection (f : E → E → F) (hf : IsSignTable f) (g : E) :
    labelQuadratic (groundSection f g) = f g g :=
  ground_quadratic_formula f hf g

theorem labelQuadratic_groundSection_nonzero (f : E → E → F) (hf : IsSignTable f)
    {g : E} (hg : g ≠ 0) :
    labelQuadratic (groundSection f g) = 1 := by
  rw [labelQuadratic_groundSection f hf]
  exact hf.diagonal g hg

private theorem labelQuadratic_add (x y : Label) :
    labelQuadratic (x + y) = labelQuadratic x + labelQuadratic y +
      (x.1 0 * y.2 0 + x.1 1 * y.2 1 + x.1 2 * y.2 2 +
       y.1 0 * x.2 0 + y.1 1 * x.2 1 + y.1 2 * x.2 2) := by
  simp only [labelQuadratic, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

private def quadraticPolar (x y : Label) : F :=
  x.1 0 * y.2 0 + x.1 1 * y.2 1 + x.1 2 * y.2 2 +
    y.1 0 * x.2 0 + y.1 1 * x.2 1 + y.1 2 * x.2 2

private theorem labelQuadratic_add_polar (x y : Label) :
    labelQuadratic (x + y) = labelQuadratic x + labelQuadratic y + quadraticPolar x y := by
  exact labelQuadratic_add x y

private theorem quadraticPolar_add_right (x y z : Label) :
    quadraticPolar x (y + z) = quadraticPolar x y + quadraticPolar x z := by
  simp only [quadraticPolar, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

private theorem quadraticPolar_sum_right {α : Type}
    (x : Label) (s : Finset α) (q : α → Label)
    (hp : ∀ j ∈ s, quadraticPolar x (q j) = 1) :
    quadraticPolar x (s.sum q) = (s.card : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadraticPolar]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, quadraticPolar_add_right]
      have hpa := hp a (Finset.mem_insert_self a s)
      have hps : ∀ j ∈ s, quadraticPolar x (q j) = 1 := by
        intro j hj
        exact hp j (Finset.mem_insert_of_mem hj)
      rw [hpa, ih hps]
      have hcard : (insert a s).card = s.card + 1 := by
        rw [← Finset.cons_eq_insert]
        exact Finset.card_cons ha
      rw [hcard]
      simp [Nat.cast_add]
      ring

private theorem quadratic_sum_formula {α : Type}
    (s : Finset α) (q : α → Label)
    (hq : ∀ i ∈ s, labelQuadratic (q i) = 1)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → quadraticPolar (q i) (q j) = 1) :
    labelQuadratic (s.sum q) =
      ((s.card + Nat.choose s.card 2 : Nat) : F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [labelQuadratic]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, labelQuadratic_add_polar]
      have hqa := hq a (Finset.mem_insert_self a s)
      have hqs : ∀ i ∈ s, labelQuadratic (q i) = 1 := by
        intro i hi
        exact hq i (Finset.mem_insert_of_mem hi)
      have hps : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → quadraticPolar (q i) (q j) = 1 := by
        intro i hi j hj hne
        exact hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hne
      rw [ih hqs hps]
      have hpolar : quadraticPolar (q a) (s.sum q) = (s.card : F) := by
        apply quadraticPolar_sum_right
        intro j hj
        have hne : a ≠ j := by
          intro h
          subst j
          exact ha hj
        exact hp a (Finset.mem_insert_self a s) j
          (Finset.mem_insert_of_mem hj) hne
      rw [hpolar]
      rw [hqa]
      have hcard : (insert a s).card = s.card + 1 := by
        rw [← Finset.cons_eq_insert]
        exact Finset.card_cons ha
      rw [hcard]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring_nf

private theorem quadratic_sum_weighted {α : Type}
    (s : Finset α) (q : α → Label) (c : α → F)
    (hq : ∀ i ∈ s, labelQuadratic (q i) = 1)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → quadraticPolar (q i) (q j) = 1) :
    labelQuadratic (s.sum (fun i => c i • q i)) =
      (((s.filter (fun i => c i = 1)).card +
        Nat.choose (s.filter (fun i => c i = 1)).card 2 : Nat) : F) := by
  classical
  let t := s.filter (fun i => c i = 1)
  have hsum : t.sum q = s.sum (fun i => c i • q i) := by
    dsimp [t]
    refine Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _) ?_ ?_
    · intro i hi
      have hmem := Finset.mem_sdiff.mp hi
      have hnot := hmem.2
      have hci : c i = 0 := by
        have hcases : ∀ z : F, z = 0 ∨ z = 1 := by
          intro z
          revert z
          decide
        rcases hcases (c i) with hci | hci
        · exact hci
        · exact (hnot (Finset.mem_filter.mpr ⟨hmem.1, hci⟩)).elim
      simp [hci]
    · intro i hi
      simp [(Finset.mem_filter.mp hi).2]
  rw [← hsum]
  exact quadratic_sum_formula t q
    (by intro i hi; exact hq i (Finset.mem_filter.mp hi |>.1))
    (by
      intro i hi j hj hne
      exact hp i (Finset.mem_filter.mp hi |>.1) j (Finset.mem_filter.mp hj |>.1) hne)

private theorem ground_pairing_formula (f : E → E → F) (hf : IsSignTable f)
    (g h : E) :
    (groundSection f g).1 0 * (groundSection f h).2 0 +
      (groundSection f g).1 1 * (groundSection f h).2 1 +
      (groundSection f g).1 2 * (groundSection f h).2 2 +
      (groundSection f h).1 0 * (groundSection f g).2 0 +
      (groundSection f h).1 1 * (groundSection f g).2 1 +
      (groundSection f h).1 2 * (groundSection f g).2 2 =
      f g h + f h g := by
  calc
    _ = g 0 * f h (unit 0) + g 1 * f h (unit 1) + g 2 * f h (unit 2) +
          h 0 * f g (unit 0) + h 1 * f g (unit 1) + h 2 * f g (unit 2) := by
      simp [groundSection, ell]
    _ = f h g + f g h := by
      rw [eval_coords f hf h g, eval_coords f hf g h]
      ring
    _ = f g h + f h g := by ring

/-- Distinct nonzero ground sections have polar pairing one. -/
theorem labelQuadratic_groundSection_polar
    (f : E → E → F) (hf : IsSignTable f) {g h : E}
    (hg : g ≠ 0) (hh : h ≠ 0) (hne : g ≠ h) :
    labelQuadratic (groundSection f g + groundSection f h) =
      labelQuadratic (groundSection f g) + labelQuadratic (groundSection f h) + 1 := by
  rw [labelQuadratic_add, ground_pairing_formula f hf]
  rw [hf.opposite g h hg hh hne]

private def sectionAt (f : E → E → F) : Fin 7 → Label :=
  ![groundSection f (unit 0), groundSection f (unit 1), groundSection f (unit 2),
    groundSection f (unit 0 + unit 1), groundSection f (unit 0 + unit 2),
    groundSection f (unit 1 + unit 2),
    groundSection f (unit 0 + unit 1 + unit 2)]

private theorem fullMap_sum (f : E → E → F) (hf : IsSignTable f) (c : Coeff) :
    fullMap f c = (Finset.univ : Finset (Fin 7)).sum (fun i => c i • sectionAt f i) := by
  change sixMap f (c 0, c 1, c 2, c 3, c 4, c 5) +
      c 6 • sixMap f (1, 1, 1, 1, 1, 1) = _
  rw [sixMap_explicit, sixMap_allOnes_explicit f hf]
  simp only [Fin.sum_univ_succ]
  simp [sectionAt, groundSection, smul_add, add_smul]
  constructor <;> abel

private theorem sectionAt_ground_nonzero (f : E → E → F) (i : Fin 7) :
    (sectionAt f i).1 ≠ 0 := by
  fin_cases i
  · intro h
    change unit 0 = 0 at h
    have h0 := congrFun h 0
    simp [unit] at h0
  · intro h
    change unit 1 = 0 at h
    have h1 := congrFun h 1
    simp [unit] at h1
  · intro h
    change unit 2 = 0 at h
    have h2 := congrFun h 2
    simp [unit] at h2
  · intro h
    change unit 0 + unit 1 = 0 at h
    have h0 := congrFun h 0
    simp [unit] at h0
  · intro h
    change unit 0 + unit 2 = 0 at h
    have h0 := congrFun h 0
    simp [unit] at h0
  · intro h
    change unit 1 + unit 2 = 0 at h
    have h1 := congrFun h 1
    simp [unit] at h1
  · intro h
    change unit 0 + unit 1 + unit 2 = 0 at h
    have h0 := congrFun h 0
    simp [unit] at h0

private theorem sectionAt_quadratic_one (f : E → E → F) (hf : IsSignTable f)
    (i : Fin 7) : labelQuadratic (sectionAt f i) = 1 := by
  fin_cases i <;> simp [sectionAt]
  all_goals apply labelQuadratic_groundSection_nonzero f hf <;> decide

private theorem ground_polar_value (f : E → E → F) (hf : IsSignTable f)
    {g h : E} (hg : g ≠ 0) (hh : h ≠ 0) (hne : g ≠ h) :
    quadraticPolar (groundSection f g) (groundSection f h) = 1 := by
  calc
    quadraticPolar (groundSection f g) (groundSection f h) =
        labelQuadratic (groundSection f g + groundSection f h) +
          labelQuadratic (groundSection f g) + labelQuadratic (groundSection f h) := by
            rw [labelQuadratic_add_polar]
            ring_nf
            simp [show (2 : F) = 0 by decide]
    _ = 1 := by
      rw [labelQuadratic_groundSection_polar f hf hg hh hne,
        labelQuadratic_groundSection_nonzero f hf hg,
        labelQuadratic_groundSection_nonzero f hf hh]
      decide

private theorem sectionAt_polar (f : E → E → F) (hf : IsSignTable f)
    {i j : Fin 7} (hne : i ≠ j) :
    quadraticPolar (sectionAt f i) (sectionAt f j) = 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [sectionAt] <;>
    apply ground_polar_value f hf <;> decide

/-- The seven-section quadratic parity is the parity of the number of selected
sections plus the parity of their pairwise intersections.  Since every section
has value one and every distinct pair has polar value one, this is
`binom (shortWeight c + 1) 2` in `F₂`. -/
theorem labelQuadratic_fullMap (f : E → E → F) (hf : IsSignTable f) (c : Coeff) :
    labelQuadratic (fullMap f c) =
      ((Nat.choose (shortWeight c + 1) 2 : Nat) : F) := by
  rw [fullMap_sum f hf]
  have h := quadratic_sum_weighted (Finset.univ : Finset (Fin 7)) (sectionAt f) c
    (by intro i hi; exact sectionAt_quadratic_one f hf i)
    (by
      intro i hi j hj hne
      exact sectionAt_polar f hf hne)
  simpa [shortWeight, Nat.choose_succ_succ, Nat.choose_one_right] using h

#print axioms labelQuadratic_groundSection
#print axioms labelQuadratic_groundSection_polar
#print axioms labelQuadratic_fullMap

end D5.S3.VertexAlgebra.MonsterShortSupportSpin
