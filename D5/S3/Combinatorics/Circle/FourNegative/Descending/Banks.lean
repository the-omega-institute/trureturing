/- GID: D5/S3/Combinatorics/Circle/FourNegative/Descending/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-banks-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-labels)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Dyadic reserve banks with empty middle intervals and literal first-bank length. -/
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Arithmetic
import Mathlib.Algebra.Order.Interval.Finset.Basic

/-! Physical reserve banks, exact masses and the literal first-bank length. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.Descending

private def bank (a H E F : ℕ) : Fin 4 → Finset ℕ :=
  ![{H} ∪ Finset.Ico (H+2) (a-1), {H+1} ∪ Finset.Ico E H,
    Finset.Ico F E, Finset.range F]

private def shift (s : ℕ) (P : Finset ℕ) : Finset ℕ := P.image (s+·)

private theorem mem_shift (s i : ℕ) (P : Finset ℕ) :
    i ∈ shift s P ↔ ∃ j ∈ P, s+j=i := by simp [shift]

private theorem image_Ico (s l n : ℕ) :
    (Finset.Ico l n).image (s+·) = Finset.Ico (s+l) (s+n) := by
  exact Finset.image_add_left_Ico l n s

private theorem image_range (s n : ℕ) :
    (Finset.range n).image (s+·) = Finset.Ico s (s+n) := by
  simpa only [Finset.range_eq_Ico, Nat.add_zero] using
    Finset.image_add_left_Ico 0 n s

private def selected (a b c d : ℕ) : Fin 3 → Finset ℕ :=
  let H := a-d-2
  let E := a-c-1
  let F := a-b-1
  ![shift (d+c+b) (bank a H E F 0),
    Finset.range (d-1) ∪ shift (d+c+b) (bank a H E F 1),
    shift d (Finset.range (c-1)) ∪ shift (d+c+b) (bank a H E F 2)]

private theorem selected_good (a b c d : ℕ)
    (hd : 2 ≤ d) (hdc : d < c) (hcb : c ≤ b) (hba : b < a) :
    (∀ r : Fin 3, ∀ i ∈ selected a b c d r,
      i < a+b+c+d ∧ i ≠ a+b+c+d-1 ∧ i ≠ d-1 ∧ i ≠ d+c-1 ∧ i ≠ d+c+b-1) ∧
    (∀ r s : Fin 3, r ≠ s → Disjoint (selected a b c d r) (selected a b c d s)) := by
  have g0 : ∀ i ∈ selected a b c d 0,
      i < a+b+c+d ∧ i ≠ a+b+c+d-1 ∧ i ≠ d-1 ∧ i ≠ d+c-1 ∧ i ≠ d+c+b-1 := by
    intro i hi
    simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,shift,
      Finset.image_union,Finset.image_singleton,image_Ico,image_range,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,Finset.mem_range] at hi
    omega
  have g1 : ∀ i ∈ selected a b c d 1,
      i < a+b+c+d ∧ i ≠ a+b+c+d-1 ∧ i ≠ d-1 ∧ i ≠ d+c-1 ∧ i ≠ d+c+b-1 := by
    intro i hi
    simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,shift,
      Finset.image_union,Finset.image_singleton,image_Ico,image_range,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,Finset.mem_range] at hi
    omega
  have g2 : ∀ i ∈ selected a b c d 2,
      i < a+b+c+d ∧ i ≠ a+b+c+d-1 ∧ i ≠ d-1 ∧ i ≠ d+c-1 ∧ i ≠ d+c+b-1 := by
    intro i hi
    simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,shift,
      Finset.image_union,Finset.image_singleton,image_Ico,image_range,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,Finset.mem_range] at hi
    omega
  have d01 : Disjoint (selected a b c d 0) (selected a b c d 1) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,shift,
      Finset.image_union,Finset.image_singleton,image_Ico,image_range,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,Finset.mem_range] at hi hj
    omega
  have d02 : Disjoint (selected a b c d 0) (selected a b c d 2) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,shift,
      Finset.image_union,Finset.image_singleton,image_Ico,image_range,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,Finset.mem_range] at hi hj
    omega
  have d12 : Disjoint (selected a b c d 1) (selected a b c d 2) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,shift,
      Finset.image_union,Finset.image_singleton,image_Ico,image_range,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,Finset.mem_range] at hi hj
    omega
  constructor
  · intro r
    fin_cases r
    all_goals first | exact g0 | exact g1 | exact g2
  · intro r s hrs
    fin_cases r <;> fin_cases s
    all_goals first | exact (hrs rfl).elim | exact d01 | exact d02 | exact d12 |
      exact d01.symm | exact d02.symm | exact d12.symm

private theorem remainder_eq (a b c d : ℕ)
    (hd : 2 ≤ d) (hdc : d < c) (hcb : c ≤ b) (hba : b < a) :
    Finset.range (a+b+c+d) \ (selected a b c d 0 ∪ selected a b c d 1 ∪
      selected a b c d 2 ∪ {a+b+c+d-1,d-1,d+c-1,d+c+b-1}) =
    shift (d+c) (Finset.range (b-1)) ∪
      shift (d+c+b) (bank a (a-d-2) (a-c-1) (a-b-1) 3) := by
  ext i
  simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,shift,Finset.image_union,
    Finset.image_singleton,image_Ico,image_range,Finset.mem_sdiff,
    Finset.mem_union,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Ico,
    Finset.mem_range]
  omega

private theorem first_card (a b c d : ℕ)
    (hd : 2 ≤ d) (hdc : d < c) (hcb : c ≤ b) (hba : b < a) :
    (selected a b c d 0).card = d := by
  have hdis : Disjoint ({a-d-2} : Finset ℕ) (Finset.Ico (a-d-2+2) (a-1)) := by
    simp [Finset.disjoint_left] <;> omega
  simp only [selected,bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,shift]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
    Finset.card_union_of_disjoint hdis,Finset.card_singleton,Nat.card_Ico]
  omega

private theorem sum_range_two (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 : ℤ)^i = 2^n-1 := by
  simpa using geom_sum_mul (2 : ℤ) n

private theorem sum_Ico_two (l n : ℕ) (h : l ≤ n) :
    ∑ i ∈ Finset.Ico l n, (2 : ℤ)^i = 2^n-2^l := by
  simpa using geom_sum_Ico_mul (2 : ℤ) h

private theorem bank_masses (a H E F : ℕ) (hh : H+2 ≤ a-1)
    (he : E ≤ H) (hf : F ≤ E) :
    (∑ i ∈ bank a H E F 0, (2 : ℤ)^i) = 2^(a-1)-3*2^H ∧
    (∑ i ∈ bank a H E F 1, (2 : ℤ)^i) = 3*2^H-2^E ∧
    (∑ i ∈ bank a H E F 2, (2 : ℤ)^i) = 2^E-2^F := by
  have h0 : Disjoint ({H} : Finset ℕ) (Finset.Ico (H+2) (a-1)) := by
    simp [Finset.disjoint_left] <;> omega
  have h1 : Disjoint ({H+1} : Finset ℕ) (Finset.Ico E H) := by
    simp [Finset.disjoint_left] <;> omega
  simp only [bank,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [Finset.sum_union h0,Finset.sum_union h1,Finset.sum_singleton,
    Finset.sum_singleton,sum_Ico_two _ _ hh,sum_Ico_two _ _ he,sum_Ico_two _ _ hf]
  simp only [pow_add,pow_one]
  norm_num <;> (repeat' constructor <;> ring)

private theorem shift_sum (f : ℕ → ℤ) (s : ℕ) (P : Finset ℕ) (B : ℤ)
    (hf : ∀ j ∈ P, f (s+j) = (2 : ℤ)^j*B) :
    (∑ i ∈ shift s P, f i) = (∑ j ∈ P, (2 : ℤ)^j)*B := by
  rw [shift,Finset.sum_image (by intro i hi j hj he; exact Nat.add_left_cancel he)]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl hf

private theorem selected_mass (a b c d : ℕ)
    (hd : 2 ≤ d) (hdc : d < c) (hcb : c ≤ b) (hba : b < a)
    (f : ℕ → ℤ) (U V X : ℤ)
    (hU : ∀ i < d-1, f i = (2 : ℤ)^i*U)
    (hV : ∀ i < c-1, f (d+i) = (2 : ℤ)^i*V)
    (hX : ∀ i < a-1, f (d+c+b+i) = (2 : ℤ)^i*X) :
    (∑ i ∈ selected a b c d 0, f i) = (2^(a-1)-3*2^(a-d-2))*X ∧
    (∑ i ∈ selected a b c d 1, f i) = (2^(d-1)-1)*U+(3*2^(a-d-2)-2^(a-c-1))*X ∧
    (∑ i ∈ selected a b c d 2, f i) = (2^(c-1)-1)*V+(2^(a-c-1)-2^(a-b-1))*X := by
  have hbnd (r : Fin 4) (i : ℕ) (hi : i ∈ bank a (a-d-2) (a-c-1) (a-b-1) r) : i < a-1 := by
    fin_cases r <;> dsimp [bank] at hi
    all_goals try simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_Ico,Finset.mem_range] at hi
    all_goals omega
  have hsum := bank_masses a (a-d-2) (a-c-1) (a-b-1) (by omega) (by omega) (by omega)
  have hs (r : Fin 4) := shift_sum f (d+c+b) (bank a (a-d-2) (a-c-1) (a-b-1) r) X
    (fun i hi => hX i (hbnd r i hi))
  have hdis0 : Disjoint (Finset.range (d-1))
      (shift (d+c+b) (bank a (a-d-2) (a-c-1) (a-b-1) 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    rw [mem_shift] at hj
    have := Finset.mem_range.mp hi
    omega
  have hdis1 : Disjoint (shift d (Finset.range (c-1)))
      (shift (d+c+b) (bank a (a-d-2) (a-c-1) (a-b-1) 2)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    rw [mem_shift] at hi hj
    simp only [Finset.mem_range] at hi
    omega
  have hu : (∑ i ∈ Finset.range (d-1), f i) = (2^(d-1)-1)*U := by
    rw [←sum_range_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact hU i (Finset.mem_range.mp hi)
  have hv := shift_sum f d (Finset.range (c-1)) V (fun i hi => hV i (Finset.mem_range.mp hi))
  rw [sum_range_two] at hv
  simp only [selected,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [Finset.sum_union hdis0,Finset.sum_union hdis1,hu,hv,hs 0,hs 1,hs 2,
    hsum.1,hsum.2.1,hsum.2.2]
  exact ⟨rfl,rfl,rfl⟩

end D5.S3.Combinatorics.Circle.FourNegative.Descending
