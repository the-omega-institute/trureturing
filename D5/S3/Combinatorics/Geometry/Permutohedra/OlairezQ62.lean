/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic differences conjugate the source dihedral orbit hull to the signed wrap hull. -/
import D5.S3.Arith.Primes.CyclicDifferencePrimeContent
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-! The standard orbit in Olairez, arXiv:2610.28672v2, Equations (2), (5), (7).
A coordinate is indexed by its residue in ZMod n. The zero residue is paper label n. -/

namespace OlairezQ62

open Finset

noncomputable section

abbrev Coordinates (n : ℕ) := ZMod n → ℝ

variable {n : ℕ}

def paperLabel (i : ZMod n) : ℕ := (i - 1).val + 1

private theorem label_bounds [NeZero n] (i : ZMod n) :
    1 ≤ paperLabel i ∧ paperLabel i ≤ n := by
  have h := ZMod.val_lt (i - 1)
  unfold paperLabel
  omega

private theorem label_cast [NeZero n] (i : ZMod n) : (paperLabel i : ZMod n) = i := by
  unfold paperLabel
  rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val, sub_add_cancel]

private theorem label_of_cast [NeZero n] {a : ℕ} (h₁ : 1 ≤ a) (h₂ : a ≤ n) :
    paperLabel (a : ZMod n) = a := by
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = b + 1 := ⟨a - 1, by omega⟩
  have hb : b < n := by omega
  unfold paperLabel
  rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, ZMod.val_natCast_of_lt hb]

private theorem label_zero [NeZero n] : paperLabel (0 : ZMod n) = n := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  simpa only [ZMod.natCast_self] using (label_of_cast (n := n) hn le_rfl)

private theorem label_injective [NeZero n] : Function.Injective (paperLabel (n := n)) := by
  intro i j h
  simpa only [label_cast] using congrArg (fun a : ℕ => (a : ZMod n)) h

/-- Literal paper labels, represented by the integers 1 through n. -/
def PaperLabels (n : ℕ) := {a : ℕ // 1 ≤ a ∧ a ≤ n}

/-- Residues written in the paper's convention, with zero represented by n. -/
def paperLabelsEquiv (n : ℕ) [NeZero n] : ZMod n ≃ PaperLabels n where
  toFun i := ⟨paperLabel i, label_bounds i⟩
  invFun a := (a.val : ZMod n)
  left_inv := label_cast
  right_inv a := Subtype.ext (label_of_cast a.property.1 a.property.2)

def shift (a : ZMod n) : Equiv.Perm (ZMod n) :=
  (Equiv.subRight a).symm

def reflection (a : ZMod n) : Equiv.Perm (ZMod n) where
  toFun i := a - i
  invFun i := a - i
  left_inv i := sub_sub_cancel a i
  right_inv i := sub_sub_cancel a i

private theorem reflection_inv (a : ZMod n) : (reflection a)⁻¹ = reflection a := by
  apply Equiv.ext
  intro i
  rfl

def s1 (n : ℕ) : Equiv.Perm (ZMod n) := reflection 3
def s2 (n : ℕ) : Equiv.Perm (ZMod n) := reflection 2

def sourceGroup (n : ℕ) : Subgroup (Equiv.Perm (ZMod n)) :=
  Subgroup.closure {s1 n, s2 n}

/-- The column-vector action associated to the permutation matrix. -/
def act (g : Equiv.Perm (ZMod n)) (x : Coordinates n) : Coordinates n :=
  fun i => x (g.symm i)

private theorem act_one (x : Coordinates n) : act 1 x = x := rfl

private theorem act_mul (g h : Equiv.Perm (ZMod n)) (x : Coordinates n) :
    act (g * h) x = act g (act h x) := rfl

def permutationMatrix (g : Equiv.Perm (ZMod n)) : Matrix (ZMod n) (ZMod n) ℝ :=
  Equiv.Perm.permMatrix ℝ g.symm

private theorem matrix_action [NeZero n] (g : Equiv.Perm (ZMod n)) (x : Coordinates n) :
    (permutationMatrix g).mulVec x = act g x :=
  Matrix.permMatrix_mulVec (v := x) g.symm

/-- The nonzero column label in each row of the two matrices in Equation (2). -/
def paperColumn1 (n i : ℕ) : ℕ :=
  if i = 1 then 2 else if i = 2 then 1 else n + 3 - i

def paperColumn2 (n i : ℕ) : ℕ :=
  if i = 1 then 1 else n + 2 - i

private theorem s1_column [NeZero n] (hn : 3 ≤ n) (i : ZMod n) :
    paperLabel ((s1 n).symm i) = paperColumn1 n (paperLabel i) := by
  change paperLabel (3 - i) = paperColumn1 n (paperLabel i)
  obtain ⟨hlo, hhi⟩ := label_bounds i
  have hi := label_cast i
  by_cases h₁ : paperLabel i = 1
  · have hi₁ : i = 1 := by simpa only [h₁, Nat.cast_one] using hi.symm
    simp only [paperColumn1, ite_eq_left h₁]
    rw [hi₁, show (3 : ZMod n) - 1 = ((2 : ℕ) : ZMod n) by norm_num]
    exact label_of_cast (by omega) (by omega)
  by_cases h₂ : paperLabel i = 2
  · have hi₂ : i = 2 := by simpa only [h₂, Nat.cast_ofNat] using hi.symm
    simp only [paperColumn1, ite_eq_right h₁, ite_eq_left h₂]
    rw [hi₂, show (3 : ZMod n) - 2 = ((1 : ℕ) : ZMod n) by norm_num]
    exact label_of_cast (by omega) (by omega)
  · have hsub : paperLabel i ≤ n + 3 := by omega
    have hcast : ((n + 3 - paperLabel i : ℕ) : ZMod n) = 3 - i := by
      rw [Nat.cast_sub hsub, Nat.cast_add, hi, ZMod.natCast_self, zero_add, Nat.cast_ofNat]
    rw [paperColumn1, ite_eq_right h₁, ite_eq_right h₂, ← hcast]
    exact label_of_cast (by omega) (by omega)

private theorem s2_column [NeZero n] (hn : 3 ≤ n) (i : ZMod n) :
    paperLabel ((s2 n).symm i) = paperColumn2 n (paperLabel i) := by
  change paperLabel (2 - i) = paperColumn2 n (paperLabel i)
  obtain ⟨hlo, hhi⟩ := label_bounds i
  have hi := label_cast i
  by_cases h₁ : paperLabel i = 1
  · have hi₁ : i = 1 := by simpa only [h₁, Nat.cast_one] using hi.symm
    simp only [paperColumn2, ite_eq_left h₁]
    rw [hi₁, show (2 : ZMod n) - 1 = ((1 : ℕ) : ZMod n) by norm_num]
    exact label_of_cast (by omega) (by omega)
  · have hsub : paperLabel i ≤ n + 2 := by omega
    have hcast : ((n + 2 - paperLabel i : ℕ) : ZMod n) = 2 - i := by
      rw [Nat.cast_sub hsub, Nat.cast_add, hi, ZMod.natCast_self, zero_add, Nat.cast_ofNat]
    rw [paperColumn2, ite_eq_right h₁, ← hcast]
    exact label_of_cast (by omega) (by omega)

private theorem equation_two [NeZero n] (hn : 3 ≤ n) (i j : ZMod n) :
    permutationMatrix (s1 n) i j =
      (if paperLabel j = paperColumn1 n (paperLabel i) then 1 else 0) ∧
    permutationMatrix (s2 n) i j =
      (if paperLabel j = paperColumn2 n (paperLabel i) then 1 else 0) := by
  constructor
  · simp only [permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply,
      Pi.single_apply, eq_comm, ← s1_column hn i, (label_injective (n := n)).eq_iff]
  · simp only [permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply,
      Pi.single_apply, eq_comm, ← s2_column hn i, (label_injective (n := n)).eq_iff]

private theorem shift_zero : shift (0 : ZMod n) = 1 := by
  apply Equiv.ext
  intro i
  exact add_zero i

private theorem shift_mul (a b : ZMod n) : shift a * shift b = shift (a + b) := by
  apply Equiv.ext
  intro i
  change (i + b) + a = i + (a + b)
  abel

private theorem reflection_mul (a b : ZMod n) :
    reflection a * reflection b = shift (a - b) := by
  apply Equiv.ext
  intro i
  change a - (b - i) = i + (a - b)
  abel

private theorem shift_mul_reflection (a b : ZMod n) :
    shift a * reflection b = reflection (a + b) := by
  apply Equiv.ext
  intro i
  change (b - i) + a = (a + b) - i
  abel

private theorem reflection_mul_shift (a b : ZMod n) :
    reflection a * shift b = reflection (a - b) := by
  apply Equiv.ext
  intro i
  change a - (i + b) = (a - b) - i
  abel

private theorem shift_inv (a : ZMod n) : (shift a)⁻¹ = shift (-a) := by
  apply Equiv.ext
  intro i
  exact sub_eq_add_neg i a

private theorem shift_pow (a : ZMod n) (m : ℕ) :
    (shift a) ^ m = shift ((m : ZMod n) * a) := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, shift_zero]
  | succ m ih =>
    rw [pow_succ, ih, shift_mul, Nat.cast_succ, add_mul, one_mul]

private theorem generator_product : s2 n * s1 n = shift (-1 : ZMod n) := by
  rw [s2, s1, reflection_mul, show (2 : ZMod n) - 3 = -1 by ring]

private theorem opposite_product : s1 n * s2 n = shift (1 : ZMod n) := by
  rw [s1, s2, reflection_mul, show (3 : ZMod n) - 2 = 1 by ring]

private theorem reversal_word : s2 n * s1 n * s2 n = reflection (1 : ZMod n) := by
  rw [generator_product, s2, shift_mul_reflection, show (-1 : ZMod n) + 2 = 1 by ring]

private theorem s1_mem : s1 n ∈ sourceGroup n :=
  Subgroup.subset_closure (by simp)

private theorem s2_mem : s2 n ∈ sourceGroup n :=
  Subgroup.subset_closure (by simp)

private theorem shift_mem [NeZero n] (a : ZMod n) : shift a ∈ sourceGroup n := by
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
  have h : shift (1 : ZMod n) ∈ sourceGroup n := by
    rw [← opposite_product]
    exact (sourceGroup n).mul_mem s1_mem s2_mem
  simpa only [shift_pow, mul_one] using (sourceGroup n).pow_mem h m

private theorem reflection_mem [NeZero n] (a : ZMod n) :
    reflection a ∈ sourceGroup n := by
  have h : shift (a - 2) * reflection 2 ∈ sourceGroup n :=
    (sourceGroup n).mul_mem (shift_mem (a - 2)) s2_mem
  simpa only [shift_mul_reflection, sub_add_cancel] using h

private theorem group_normal_forms [NeZero n] (g : Equiv.Perm (ZMod n)) :
    g ∈ sourceGroup n ↔ (∃ a, g = shift a) ∨ (∃ a, g = reflection a) := by
  constructor
  · intro hg
    unfold sourceGroup at hg
    refine Subgroup.closure_induction
      (p := fun g _ => (∃ a, g = shift a) ∨ (∃ a, g = reflection a)) ?_ ?_ ?_ ?_ hg
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact Or.inr ⟨3, rfl⟩
      · have h := Set.mem_singleton_iff.mp hx
        subst x
        exact Or.inr ⟨2, rfl⟩
    · exact Or.inl ⟨0, shift_zero.symm⟩
    · intro x y _ _ hx hy
      rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
        rcases hy with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a + b, shift_mul a b⟩
      · exact Or.inr ⟨a + b, shift_mul_reflection a b⟩
      · exact Or.inr ⟨a - b, reflection_mul_shift a b⟩
      · exact Or.inl ⟨a - b, reflection_mul a b⟩
    · intro x _ hx
      rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact Or.inl ⟨-a, shift_inv a⟩
      · exact Or.inr ⟨a, reflection_inv a⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact shift_mem a
    · exact reflection_mem a

def rho (n : ℕ) : Coordinates n := fun i => paperLabel i

def center (n : ℕ) : Coordinates n := fun _ => ((n : ℝ) + 1) / 2

/-- One-based rotation labels as in Equation (5). -/
def r (j : ZMod n) : Coordinates n := fun i => rho n (i + j - 1)

/-- The antipodal labeling of Equation (7). -/
def f (j : ZMod n) : Coordinates n := fun i => (n : ℝ) + 1 - r j i

private theorem rho_injective [NeZero n] : Function.Injective (rho n) := by
  intro i j h
  apply label_injective
  change (paperLabel i : ℝ) = (paperLabel j : ℝ) at h
  exact_mod_cast h

private theorem rho_reversal [NeZero n] (i : ZMod n) :
    rho n (1 - i) = (n : ℝ) + 1 - rho n i := by
  obtain ⟨hlo, hhi⟩ := label_bounds i
  have hsub : paperLabel i ≤ n + 1 := by omega
  have hcast : ((n + 1 - paperLabel i : ℕ) : ZMod n) = 1 - i := by
    rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one, label_cast, ZMod.natCast_self, zero_add]
  change (paperLabel (1 - i) : ℝ) = (n : ℝ) + 1 - paperLabel i
  rw [← hcast, label_of_cast (by omega : 1 ≤ n + 1 - paperLabel i)
    (by omega : n + 1 - paperLabel i ≤ n), Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]

private theorem shift_r (j : ZMod n) : act (shift (1 - j)) (rho n) = r j := by
  funext i
  change rho n (i - (1 - j)) = rho n (i + j - 1)
  congr 1
  abel

private theorem reflection_f [NeZero n] (j : ZMod n) :
    act (reflection (2 - j)) (rho n) = f j := by
  funext i
  change rho n (2 - j - i) = (n : ℝ) + 1 - rho n (i + j - 1)
  rw [show (2 : ZMod n) - j - i = 1 - (i + j - 1) by ring, rho_reversal]

private theorem equation_five [NeZero n] (j : ZMod n) :
    act ((s2 n * s1 n) ^ (j - 1).val) (rho n) = r j := by
  rw [generator_product, shift_pow, ZMod.natCast_zmod_val, mul_neg, mul_one,
    show -(j - 1) = 1 - j by abel]
  exact shift_r j

private theorem equation_seven_word [NeZero n] (j : ZMod n) :
    act ((s2 n * s1 n) ^ (j - 1).val * (s2 n * s1 n * s2 n)) (rho n) = f j := by
  rw [reversal_word, generator_product, shift_pow, ZMod.natCast_zmod_val, mul_neg, mul_one,
    shift_mul_reflection, show -(j - 1) + 1 = 2 - j by ring]
  exact reflection_f j

def orbit (n : ℕ) : Set (Coordinates n) :=
  {x | ∃ g ∈ sourceGroup n, act g (rho n) = x}

private theorem orbit_eq [NeZero n] :
    orbit n = Set.range (r (n := n)) ∪ Set.range (f (n := n)) := by
  ext x
  constructor
  · rintro ⟨g, hg, h⟩
    rcases (group_normal_forms g).mp hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · left
      refine ⟨1 - a, ?_⟩
      rw [← shift_r, show 1 - (1 - a) = a by abel]
      exact h
    · right
      refine ⟨2 - a, ?_⟩
      rw [← reflection_f, show 2 - (2 - a) = a by abel]
      exact h
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨shift (1 - j), shift_mem _, shift_r j⟩
    · exact ⟨reflection (2 - j), reflection_mem _, reflection_f j⟩

private theorem two_nonzero [NeZero n] (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have hnat : ((2 : ℕ) : ZMod n) = 0 := by simpa only [Nat.cast_ofNat] using h
  have hval := congrArg ZMod.val hnat
  rw [ZMod.val_natCast_of_lt (n := n) (a := 2) (by omega), ZMod.val_zero] at hval
  omega

private theorem reverse_action_fails [NeZero n] (hn : 3 ≤ n) :
    (fun i => rho n ((s2 n * s1 n) i)) ≠ r (2 : ZMod n) := by
  intro h
  have hi := congrFun h (1 : ZMod n)
  rw [generator_product] at hi
  change rho n (1 + (-1)) = rho n (1 + 2 - 1) at hi
  have he := rho_injective hi
  exact (two_nonzero hn) (by linear_combination -he)

private theorem reversal_on_rotations [NeZero n] (j : ZMod n) :
    act (s2 n * s1 n * s2 n) (r j) = f (2 - j) := by
  rw [reversal_word, ← shift_r, ← act_mul, reflection_mul_shift,
    show 1 - (1 - j) = j by abel]
  calc
    act (reflection j) (rho n) = act (reflection (2 - (2 - j))) (rho n) :=
      congrArg (fun k : ZMod n => act (reflection k) (rho n)) (sub_sub_cancel 2 j).symm
    _ = f (2 - j) := reflection_f (2 - j)

private theorem no_fixed_reflection [NeZero n] (hn : 3 ≤ n) :
    ¬ ∃ a : ZMod n, ∀ j : ZMod n, act (reflection a) (r j) = f j := by
  rintro ⟨a, h⟩
  have hindex (j : ZMod n) : a - (1 - j) = 2 - j := by
    have hj := h j
    rw [← shift_r, ← act_mul, reflection_mul_shift, ← reflection_f] at hj
    have he := congrFun hj (0 : ZMod n)
    change rho n ((a - (1 - j)) - 0) = rho n ((2 - j) - 0) at he
    simpa only [sub_zero] using rho_injective he
  have ha : a = 1 := by
    have he := hindex 1
    linear_combination he
  have he := hindex 2
  rw [ha] at he
  have hzero : (2 : ZMod n) = 0 := by linear_combination he
  exact two_nonzero hn hzero

def sumZero (n : ℕ) [NeZero n] : Submodule ℝ (Coordinates n) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, x i = 0 at hx
    change ∑ i, y i = 0 at hy
    change ∑ i, (x i + y i) = 0
    rw [sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ i, x i = 0 at hx
    change ∑ i, c * x i = 0
    rw [← mul_sum, hx, mul_zero]

private theorem base_centered_sum_zero [NeZero n] :
    ∑ i : ZMod n, (rho n - center n) i = 0 := by
  have h := Equiv.sum_comp (reflection (1 : ZMod n)) (rho n - center n)
  change (∑ i : ZMod n, (rho n - center n) (1 - i)) = _ at h
  have hopposite (i : ZMod n) :
      (rho n - center n) (1 - i) = -((rho n - center n) i) := by
    change rho n (1 - i) - ((n : ℝ) + 1) / 2 = -(rho n i - ((n : ℝ) + 1) / 2)
    rw [rho_reversal]
    ring
  simp only [hopposite, sum_neg_distrib] at h
  linarith

private theorem centered_act_sum_zero [NeZero n] (g : Equiv.Perm (ZMod n)) :
    ∑ i : ZMod n, (act g (rho n) - center n) i = 0 := by
  change (∑ i : ZMod n, (rho n - center n) (g.symm i)) = 0
  rw [Equiv.sum_comp g.symm (rho n - center n)]
  exact base_centered_sum_zero

def rCentered [NeZero n] (j : ZMod n) : sumZero n :=
  ⟨r j - center n, by
    change ∑ i : ZMod n, (r j - center n) i = 0
    rw [← shift_r]
    exact centered_act_sum_zero _⟩

def fCentered [NeZero n] (j : ZMod n) : sumZero n :=
  ⟨f j - center n, by
    change ∑ i : ZMod n, (f j - center n) i = 0
    rw [← reflection_f]
    exact centered_act_sum_zero _⟩

private theorem fCentered_eq_neg [NeZero n] (j : ZMod n) :
    fCentered j = -rCentered j := by
  apply Subtype.ext
  funext i
  change (n : ℝ) + 1 - r j i - ((n : ℝ) + 1) / 2 =
    -(r j i - ((n : ℝ) + 1) / 2)
  ring

private theorem forward_sum_zero [NeZero n] (v : Coordinates n) :
    ∑ i : ZMod n, (v (i + 1) - v i) = 0 := by
  calc
    ∑ i : ZMod n, (v (i + 1) - v i) =
        ∑ i : ZMod n, (v (shift 1 i) - v (shift 1 i - 1)) := by
      simp only [show ∀ i : ZMod n, shift 1 i = i + 1 from fun _ => rfl, add_sub_cancel_right]
    _ = ∑ i : ZMod n, (v i - v (i - 1)) :=
      Equiv.sum_comp (shift (1 : ZMod n)) (fun i => v i - v (i - 1))
    _ = 0 := D5.S3.Arith.Primes.CyclicDifferencePrimeContent.sum_diff v

def forwardDifference (n : ℕ) [NeZero n] : sumZero n →ₗ[ℝ] sumZero n where
  toFun x := ⟨fun i => x.val (i + 1) - x.val i, forward_sum_zero x.val⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    change (x.val (i + 1) + y.val (i + 1)) - (x.val i + y.val i) =
      (x.val (i + 1) - x.val i) + (y.val (i + 1) - y.val i)
    ring
  map_smul' c x := by
    apply Subtype.ext
    funext i
    change c * x.val (i + 1) - c * x.val i = c * (x.val (i + 1) - x.val i)
    ring

private theorem forward_injective [NeZero n] : Function.Injective (forwardDifference n) := by
  intro x y h
  let v : Coordinates n := x.val - y.val
  have hvsum : ∑ i, v i = 0 := (x - y).property
  have hbackward (i : ZMod n) : v i - v (i - 1) = 0 := by
    have hi := congrArg (fun z : sumZero n => z.val (i - 1)) h
    change x.val (i - 1 + 1) - x.val (i - 1) =
      y.val (i - 1 + 1) - y.val (i - 1) at hi
    rw [sub_add_cancel] at hi
    change (x.val i - y.val i) - (x.val (i - 1) - y.val (i - 1)) = 0
    linarith
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hv : ∀ i, v i = 0 := D5.S3.Arith.Primes.CyclicDifferencePrimeContent.diff_injective_sum_zero hn v hvsum hbackward
  apply Subtype.ext
  funext i
  exact sub_eq_zero.mp (hv i)

def delta (n : ℕ) [NeZero n] : sumZero n ≃ₗ[ℝ] sumZero n :=
  LinearEquiv.ofInjectiveEndo (forwardDifference n) forward_injective

private theorem delta_apply [NeZero n] (x : sumZero n) (i : ZMod n) :
    (delta n x).val i = x.val (i + 1) - x.val i := rfl

def basisVector (k : ZMod n) : Coordinates n := Pi.single k 1

def wrapPoint [NeZero n] (k : ZMod n) : sumZero n :=
  ⟨fun i => 1 - (n : ℝ) * basisVector k i, by
    change (∑ i : ZMod n, (1 - (n : ℝ) * basisVector k i)) = 0
    rw [sum_sub_distrib, ← mul_sum]
    simp [basisVector, ZMod.card, nsmul_eq_mul]⟩

private theorem rho_step [NeZero n] (i : ZMod n) :
    rho n (i + 1) - rho n i = 1 - (n : ℝ) * (if i = 0 then 1 else 0) := by
  have hnext : paperLabel (i + 1) = i.val + 1 := by
    unfold paperLabel
    rw [add_sub_cancel_right]
  by_cases hi : i = 0
  · subst i
    have hlabel : paperLabel (0 : ZMod n) = n := label_zero
    change (paperLabel ((0 : ZMod n) + 1) : ℝ) - paperLabel (0 : ZMod n) =
      1 - (n : ℝ) * (if (0 : ZMod n) = 0 then 1 else 0)
    rw [hnext, hlabel, ZMod.val_zero, zero_add]
    simp
  · have hv := (ZMod.val_pos (a := i)).mpr hi
    have hlt := ZMod.val_lt i
    have hcast : ((i.val - 1 : ℕ) : ZMod n) = i - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one, ZMod.natCast_zmod_val]
    have hlabel : paperLabel i = i.val := by
      unfold paperLabel
      rw [← hcast, ZMod.val_natCast_of_lt (by omega : i.val - 1 < n)]
      omega
    simp only [rho, hnext, hlabel, Nat.cast_add, Nat.cast_one, ite_eq_right hi, mul_zero, sub_zero]
    ring

private theorem delta_r [NeZero n] (j : ZMod n) :
    delta n (rCentered j) = wrapPoint (1 - j) := by
  apply Subtype.ext
  funext i
  rw [delta_apply]
  change (rho n ((i + 1) + j - 1) - ((n : ℝ) + 1) / 2) -
      (rho n (i + j - 1) - ((n : ℝ) + 1) / 2) =
    1 - (n : ℝ) * basisVector (1 - j) i
  simp only [basisVector, Pi.single_apply]
  rw [show (i + 1) + j - 1 = (i + j - 1) + 1 by abel]
  have hstep := rho_step (i + j - 1)
  have hwrap : (i + j - 1 = 0) ↔ i = 1 - j := by
    constructor
    · intro h
      linear_combination h
    · intro h
      rw [h]
      abel
  simp only [hwrap] at hstep
  simp only [eq_comm] at hstep ⊢
  linarith

private theorem delta_f [NeZero n] (j : ZMod n) :
    delta n (fCentered j) = -wrapPoint (1 - j) := by
  rw [fCentered_eq_neg, map_neg, delta_r]

def centeredOrbit (n : ℕ) [NeZero n] : Set (sumZero n) :=
  {w | ∃ x ∈ orbit n, w.val = x - center n}

def Q (n : ℕ) : Set (Coordinates n) := convexHull ℝ (orbit n)

def centeredQ (n : ℕ) [NeZero n] : Set (sumZero n) := convexHull ℝ (centeredOrbit n)

def signedPoints (n : ℕ) [NeZero n] : Set (sumZero n) :=
  Set.range (wrapPoint (n := n)) ∪ Set.range (fun k : ZMod n => -wrapPoint k)

private theorem centeredOrbit_eq [NeZero n] :
    centeredOrbit n = Set.range (rCentered (n := n)) ∪ Set.range (fCentered (n := n)) := by
  ext w
  constructor
  · rintro ⟨x, hx, h⟩
    rw [orbit_eq] at hx
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨j, Subtype.ext h.symm⟩
    · exact Or.inr ⟨j, Subtype.ext h.symm⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨r j, ?_, rfl⟩
      rw [orbit_eq]
      exact Or.inl ⟨j, rfl⟩
    · refine ⟨f j, ?_, rfl⟩
      rw [orbit_eq]
      exact Or.inr ⟨j, rfl⟩

private theorem ambient_centeredQ [NeZero n] :
    (fun w : sumZero n => w.val) '' centeredQ n =
      (fun x : Coordinates n => x - center n) '' Q n := by
  let translation := (AffineEquiv.constVAdd ℝ (Coordinates n) (-center n)).toAffineMap
  have translation_apply : (translation : Coordinates n → Coordinates n) =
      fun x => x - center n := by
    funext x
    change -center n + x = x - center n
    abel
  change (sumZero n).subtype '' convexHull ℝ (centeredOrbit n) =
    (fun x : Coordinates n => x - center n) '' convexHull ℝ (orbit n)
  rw [← translation_apply, (sumZero n).subtype.image_convexHull, translation.image_convexHull]
  congr 1
  rw [translation_apply]
  ext w
  constructor
  · rintro ⟨v, ⟨x, hx, hv⟩, rfl⟩
    exact ⟨x, hx, hv.symm⟩
  · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨act g (rho n) - center n, centered_act_sum_zero g⟩,
      ⟨act g (rho n), ⟨g, hg, rfl⟩, rfl⟩, rfl⟩

private theorem delta_centeredOrbit [NeZero n] :
    delta n '' centeredOrbit n = signedPoints n := by
  rw [centeredOrbit_eq]
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨1 - j, (delta_r j).symm⟩
    · exact Or.inr ⟨1 - j, (delta_f j).symm⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · refine ⟨rCentered (1 - k), Or.inl ⟨1 - k, rfl⟩, ?_⟩
      rw [delta_r, show 1 - (1 - k) = k by abel]
    · refine ⟨fCentered (1 - k), Or.inr ⟨1 - k, rfl⟩, ?_⟩
      rw [delta_f, show 1 - (1 - k) = k by abel]

private theorem delta_centeredQ [NeZero n] :
    delta n '' centeredQ n = convexHull ℝ (signedPoints n) := by
  change (delta n).toLinearMap '' convexHull ℝ (centeredOrbit n) =
    convexHull ℝ (signedPoints n)
  rw [(delta n).toLinearMap.image_convexHull]
  exact congrArg (convexHull ℝ) delta_centeredOrbit

/-- The real source-coordinate conjugacy for the standard Olairez orbit. -/
theorem source_coordinate_conjugacy (n : ℕ) (hn : 3 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    paperLabel (0 : ZMod n) = n ∧
    (∀ i j : ZMod n,
      permutationMatrix (s1 n) i j =
        (if paperLabel j = paperColumn1 n (paperLabel i) then 1 else 0) ∧
      permutationMatrix (s2 n) i j =
        (if paperLabel j = paperColumn2 n (paperLabel i) then 1 else 0)) ∧
    (∀ (g : Equiv.Perm (ZMod n)) (x : Coordinates n),
      (permutationMatrix g).mulVec x = act g x) ∧
    (∀ x : Coordinates n, act 1 x = x) ∧
    (∀ (g h : Equiv.Perm (ZMod n)) (x : Coordinates n), act (g * h) x = act g (act h x)) ∧
    (s1 n * s1 n = 1 ∧ s2 n * s2 n = 1) ∧
    (∀ g : Equiv.Perm (ZMod n),
      g ∈ sourceGroup n ↔ (∃ a, g = shift a) ∨ (∃ a, g = reflection a)) ∧
    (∀ j : ZMod n,
      act ((s2 n * s1 n) ^ (j - 1).val) (rho n) = r j ∧
      act ((s2 n * s1 n) ^ (j - 1).val * (s2 n * s1 n * s2 n)) (rho n) = f j ∧
      (∀ i : ZMod n, r j i = (paperLabel (i + j - 1) : ℝ) ∧
        f j i = (n : ℝ) + 1 - r j i)) ∧
    (∀ j : ZMod n, act (s2 n * s1 n * s2 n) (r j) = f (2 - j)) ∧
    (fun i => rho n ((s2 n * s1 n) i)) ≠ r (2 : ZMod n) ∧
    (¬ ∃ a : ZMod n, ∀ j : ZMod n, act (reflection a) (r j) = f j) ∧
    orbit n = Set.range (r (n := n)) ∪ Set.range (f (n := n)) ∧
    (fun w : sumZero n => w.val) '' centeredQ n =
      (fun x : Coordinates n => x - center n) '' Q n ∧
    (∀ (x : sumZero n) (i : ZMod n), (delta n x).val i = x.val (i + 1) - x.val i) ∧
    (∀ j : ZMod n, delta n (rCentered j) = wrapPoint (1 - j) ∧
      delta n (fCentered j) = -wrapPoint (1 - j)) ∧
    delta n '' centeredQ n = convexHull ℝ (signedPoints n) := by
  letI : NeZero n := ⟨by omega⟩
  have hs : s1 n * s1 n = 1 ∧ s2 n * s2 n = 1 := by
    constructor <;> simp only [s1, s2, reflection_mul, sub_self, shift_zero]
  exact ⟨label_zero, equation_two hn, matrix_action, act_one, act_mul, hs, group_normal_forms,
    fun j => ⟨equation_five j, equation_seven_word j, fun _ => ⟨rfl, rfl⟩⟩,
    reversal_on_rotations, reverse_action_fails hn, no_fixed_reflection hn, orbit_eq,
    ambient_centeredQ, delta_apply, fun j => ⟨delta_r j, delta_f j⟩, delta_centeredQ⟩

end

end OlairezQ62
