/- GID: D5/S3/Combinatorics/Circle/FourNegative/Descending/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-banks-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-labels)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Labelled dyadic reserve banks retain empty middle banks and the exact first-bank cardinality. -/
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Arithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.Descending

private def bank (a H E F : ℕ) : Fin 4 → Finset ℕ :=
  ![{H} ∪ Finset.Ico (H+2) (a-1), {H+1} ∪ Finset.Ico E H,
    Finset.Ico F E, Finset.range F]

private def shift (s : ℕ) (P : Finset ℕ) : Finset ℕ := P.image (s+·)

private theorem mem_shift (s i : ℕ) (P : Finset ℕ) :
    i ∈ shift s P ↔ ∃ j ∈ P, s+j=i := by simp [shift]

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
  have he : a-c-1 ≤ a-d-2 := by omega
  have hf : a-b-1 ≤ a-c-1 := by omega
  constructor
  · intro r i hi
    fin_cases r <;> simp only [selected,bank,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,mem_shift,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_Ico,Finset.mem_range] at hi <;> omega
  · intro r s hrs
    apply Finset.disjoint_left.mpr
    intro i hi hj
    fin_cases r <;> fin_cases s <;>
      simp only [selected,bank,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,mem_shift,Finset.mem_union,Finset.mem_singleton,
        Finset.mem_Ico,Finset.mem_range] at hi hj <;> simp_all <;> omega

private theorem first_card (a b c d : ℕ)
    (hd : 2 ≤ d) (hdc : d < c) (hcb : c ≤ b) (hba : b < a) :
    (selected a b c d 0).card = d := by
  have hdis : Disjoint ({a-d-2} : Finset ℕ) (Finset.Ico (a-d-2+2) (a-1)) := by
    simp [Finset.disjoint_left]; omega
  simp only [selected,bank,Matrix.cons_val_zero,shift]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
    Finset.card_union_of_disjoint hdis,Finset.card_singleton,Finset.card_Ico]
  omega

private theorem sum_range_two (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 : ℤ)^i = 2^n-1 := by
  have hp := Nat.two_pow_pos n
  have hn : (∑ i ∈ Finset.range n, (2 : ℕ)^i)+1 = 2^n := by
    have h := Nat.geomSum_eq (by decide : 2 ≤ 2) n
    simp only [Nat.sub_self, Nat.reduceSub, Nat.div_one] at h
    omega
  have hn' : (∑ i ∈ Finset.range n, (2 : ℤ)^i)+1 = 2^n := by exact_mod_cast hn
  omega

private theorem sum_Ico_two (l n : ℕ) (h : l ≤ n) :
    ∑ i ∈ Finset.Ico l n, (2 : ℤ)^i = 2^n-2^l := by
  rw [Finset.sum_Ico_eq_sub _ h,sum_range_two,sum_range_two]
  ring

private theorem bank_masses (a H E F : ℕ) (hh : H+2 ≤ a-1)
    (he : E ≤ H) (hf : F ≤ E) :
    (∑ i ∈ bank a H E F 0, (2 : ℤ)^i) = 2^(a-1)-3*2^H ∧
    (∑ i ∈ bank a H E F 1, (2 : ℤ)^i) = 3*2^H-2^E ∧
    (∑ i ∈ bank a H E F 2, (2 : ℤ)^i) = 2^E-2^F := by
  have h0 : Disjoint ({H} : Finset ℕ) (Finset.Ico (H+2) (a-1)) := by
    simp [Finset.disjoint_left]; omega
  have h1 : Disjoint ({H+1} : Finset ℕ) (Finset.Ico E H) := by
    simp [Finset.disjoint_left]; omega
  simp only [bank,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [Finset.sum_union h0,Finset.sum_union h1,Finset.sum_singleton,
    Finset.sum_singleton,sum_Ico_two _ _ hh,sum_Ico_two _ _ he,sum_Ico_two _ _ hf]
  simp only [pow_add,pow_one]
  norm_num
  constructor <;> ring

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
    fin_cases r <;> simp only [bank,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_Ico,Finset.mem_range] at hi <;> omega
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
  simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [Finset.sum_union hdis0,Finset.sum_union hdis1,hu,hv,hs 0,hs 1,hs 2,
    hsum.1,hsum.2.1,hsum.2.2]
  exact ⟨rfl,rfl,rfl⟩

end D5.S3.Combinatorics.Circle.FourNegative.Descending
