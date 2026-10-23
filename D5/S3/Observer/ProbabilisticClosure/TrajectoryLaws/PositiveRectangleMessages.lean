/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive rectangular support gives a uniform guard for arbitrary nonnegative farther messages. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The two copies of a positive support rectangle surround an arbitrary middle matrix.
The farther row and column are arbitrary nonnegative messages, without a rank restriction. -/
def sandwich (T : Matrix I J ℝ) (B : Matrix J I ℝ) (α : I → ℝ) (β : J → ℝ) : ℝ :=
  ∑ j, ∑ i, (∑ k, α k*T k j)*B j i*(∑ l, T i l*β l)

/-- On nonempty rectangular support, strictly positive entries suffice for a uniform
posterior interval over every nonnegative farther row and column. No rank-one hypothesis is
used. The positive-total premise leaves zero-total atoms unnormalized. -/
theorem uniform_posterior_guard [Nonempty I] [Nonempty J]
    (T : Matrix I J ℝ) (hT : ∀ i j, 0 < T i j)
    (B₀ B₁ : Matrix J I ℝ) (hB₀ : ∀ j i, 0 ≤ B₀ j i) (hB₁ : ∀ j i, 0 ≤ B₁ j i)
    (hs₀ : 0 < ∑ j, ∑ i, B₀ j i) (hs₁ : 0 < ∑ j, ∑ i, B₁ j i) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧
      ∀ (α : I → ℝ) (β : J → ℝ), (∀ i, 0 ≤ α i) → (∀ j, 0 ≤ β j) →
        0 < sandwich T B₀ α β + sandwich T B₁ α β →
        ε ≤ sandwich T B₁ α β / (sandwich T B₀ α β + sandwich T B₁ α β) ∧
        sandwich T B₁ α β / (sandwich T B₀ α β + sandwich T B₁ α β) ≤ 1-ε := by
  classical
  let S : Finset ℝ := Finset.univ.image (fun z : I × J => T z.1 z.2)
  have hS : S.Nonempty := Finset.univ_nonempty.image _
  let m := S.min' hS
  let C := ∑ i, ∑ j, T i j
  have hm : 0 < m := by
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    change 0 < S.min' hS
    rw [← hz]
    exact hT z.1 z.2
  have hmin (i : I) (j : J) : m ≤ T i j :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)
  have hC (i : I) (j : J) : T i j ≤ C := by
    apply le_trans (Finset.single_le_sum (fun j _ => (hT i j).le) (Finset.mem_univ j))
    exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => (hT i j).le)
      (Finset.mem_univ i)
  have hCp : 0 < C := (hT (Classical.choice inferInstance) (Classical.choice inferInstance)).trans_le (hC _ _)
  let s₀ := ∑ j, ∑ i, B₀ j i
  let s₁ := ∑ j, ∑ i, B₁ j i
  let k₀ := m*m*s₀
  let k₁ := m*m*s₁
  let K := C*C*(s₀+s₁)
  have hk₀ : 0 < k₀ := mul_pos (mul_pos hm hm) hs₀
  have hk₁ : 0 < k₁ := mul_pos (mul_pos hm hm) hs₁
  have hK : 0 < K := mul_pos (mul_pos hCp hCp) (add_pos hs₀ hs₁)
  let ε := min (1/4 : ℝ) (min (k₀/K) (k₁/K))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (div_pos hk₀ hK) (div_pos hk₁ hK))
  refine ⟨ε,hε,min_le_left _ _,?_⟩
  intro α β hα hβ htotal
  let A := ∑ i, α i
  let D := ∑ j, β j
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hα i
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ => hβ j
  have hleft (j : J) : m*A ≤ ∑ i, α i*T i j ∧ (∑ i, α i*T i j) ≤ C*A := by
    constructor
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by nlinarith [mul_le_mul_of_nonneg_left (hmin i j) (hα i)]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by nlinarith [mul_le_mul_of_nonneg_left (hC i j) (hα i)]
  have hright (i : I) : m*D ≤ ∑ j, T i j*β j ∧ (∑ j, T i j*β j) ≤ C*D := by
    constructor
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hmin i j) (hβ j)
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC i j) (hβ j)
  have hln (j : J) : 0 ≤ ∑ i, α i*T i j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (hT i j).le
  have hrn (i : I) : 0 ≤ ∑ j, T i j*β j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hT i j).le (hβ j)
  have hbounds (B : Matrix J I ℝ) (hB : ∀ j i, 0 ≤ B j i) :
      (m*A)*(∑ j, ∑ i, B j i)*(m*D) ≤ sandwich T B α β ∧
      sandwich T B α β ≤ (C*A)*(∑ j, ∑ i, B j i)*(C*D) := by
    constructor
    · calc
        _ = ∑ j, ∑ i, (m*A)*B j i*(m*D) := by simp only [Finset.mul_sum,Finset.sum_mul]
        _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hleft j).1 (hB j i)) (mul_nonneg hm.le hD)).trans
              (mul_le_mul_of_nonneg_left (hright i).1 (mul_nonneg (hln j) (hB j i)))
    · calc
        _ ≤ ∑ j, ∑ i, (C*A)*B j i*(C*D) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hleft j).2 (hB j i)) (hrn i)).trans
                (mul_le_mul_of_nonneg_left (hright i).2
                  (mul_nonneg (mul_nonneg hCp.le hA) (hB j i)))
        _ = _ := by simp only [Finset.mul_sum,Finset.sum_mul]
  have hlo₀ : k₀*(A*D) ≤ sandwich T B₀ α β := by
    convert (hbounds B₀ hB₀).1 using 1 <;> dsimp [k₀,s₀] <;> ring
  have hlo₁ : k₁*(A*D) ≤ sandwich T B₁ α β := by
    convert (hbounds B₁ hB₁).1 using 1 <;> dsimp [k₁,s₁] <;> ring
  have hup : sandwich T B₀ α β + sandwich T B₁ α β ≤ K*(A*D) := by
    apply (add_le_add (hbounds B₀ hB₀).2 (hbounds B₁ hB₁).2).trans_eq
    dsimp [K,s₀,s₁]
    ring
  have hε₀ : ε*K ≤ k₀ := (le_div_iff₀ hK).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hε₁ : ε*K ≤ k₁ := (le_div_iff₀ hK).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hratio (k : ℝ) (hk : ε*K ≤ k) (f : ℝ) (hf : k*(A*D) ≤ f) :
      ε ≤ f / (sandwich T B₀ α β + sandwich T B₁ α β) := by
    apply (le_div_iff₀ htotal).mpr
    calc
      _ ≤ ε*(K*(A*D)) := mul_le_mul_of_nonneg_left hup hε.le
      _ = (ε*K)*(A*D) := by ring
      _ ≤ k*(A*D) := mul_le_mul_of_nonneg_right hk (mul_nonneg hA hD)
      _ ≤ f := hf
  have h₀ := hratio k₀ hε₀ _ hlo₀
  have h₁ := hratio k₁ hε₁ _ hlo₁
  refine ⟨h₁,?_⟩
  have he : sandwich T B₀ α β / (sandwich T B₀ α β + sandwich T B₁ α β) +
      sandwich T B₁ α β / (sandwich T B₀ α β + sandwich T B₁ α β) = 1 := by
    rw [← add_div,div_self htotal.ne']
  linarith


/-- A nonempty support rectangle; entries on it are strictly positive and all other entries
are zero. This definition places no algebraic restriction on the rank of T. -/
structure Rectangle {H : Type*} [Fintype H] (T : Matrix H H ℝ) where
  rows : Finset H
  cols : Finset H
  rows_nonempty : rows.Nonempty
  cols_nonempty : cols.Nonempty
  positive : ∀ i ∈ rows, ∀ j ∈ cols, 0 < T i j
  zero : ∀ i j, ¬(i ∈ rows ∧ j ∈ cols) → T i j = 0

private theorem sum_restrict {H : Type*} [Fintype H] (s : Finset H) (f : H → ℝ)
    (hf : ∀ i, i ∉ s → f i = 0) : ∑ i, f i = ∑ i : {i // i ∈ s}, f i.val := by
  classical
  have hh := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) f
  have hz : (∑ i : {i // i ∉ s}, f i.val) = 0 := Finset.sum_eq_zero fun i _ => hf i i.property
  rw [hz,add_zero] at hh
  convert hh.symm using 1 <;> congr 1 <;> ext i <;> simp

private theorem restrict_sandwich {H : Type*} [Fintype H]
    (T B : Matrix H H ℝ) (R : Rectangle T) (α β : H → ℝ) :
    sandwich T B α β = sandwich
      (fun (i : {i // i ∈ R.rows}) (j : {j // j ∈ R.cols}) => T i j)
      (fun (j : {j // j ∈ R.cols}) (i : {i // i ∈ R.rows}) => B j i)
      (fun i => α i.val) (fun j => β j.val) := by
  classical
  unfold sandwich
  have hzL (j : H) (hj : j ∉ R.cols) : (∑ k, α k*T k j) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [R.zero k j (fun h => hj h.2),mul_zero]
  have hzR (i : H) (hi : i ∉ R.rows) : (∑ l, T i l*β l) = 0 :=
    Finset.sum_eq_zero fun l _ => by rw [R.zero i l (fun h => hi h.1),zero_mul]
  rw [sum_restrict R.cols _ (fun j hj => by simp only [hzL j hj,zero_mul,Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_restrict R.rows _ (fun i hi => by simp only [hzR i hi,mul_zero])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_restrict R.rows (fun k => α k*T k j) (fun k hk => by
    rw [R.zero k j (fun h => hk h.1),mul_zero])]
  rw [sum_restrict R.cols (fun l => T i l*β l) (fun l hl => by
    rw [R.zero i l (fun h => hl h.2),zero_mul])]

/-- A supported positive rectangle gives a uniform actual-message posterior guard. The two
protected masses are evaluated with one common nonnegative row lambda. All farther messages
remain arbitrary, including messages yielding zero-total atoms, which are not normalized. -/
theorem supported_message_guard {H : Type*} [Fintype H]
    (T B₀ B₁ : Matrix H H ℝ) (R : Rectangle T)
    (hB₀ : ∀ j i, 0 ≤ B₀ j i) (hB₁ : ∀ j i, 0 ≤ B₁ j i)
    (initial : H → ℝ) (hinitial : ∀ i, 0 ≤ initial i)
    (h₀ : 0 < sandwich T B₀ initial (fun _ => 1))
    (h₁ : 0 < sandwich T B₁ initial (fun _ => 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧
      ∀ (α β : H → ℝ), (∀ i, 0 ≤ α i) → (∀ j, 0 ≤ β j) →
        0 < sandwich T B₀ α β + sandwich T B₁ α β →
        ε ≤ sandwich T B₁ α β / (sandwich T B₀ α β + sandwich T B₁ α β) ∧
        sandwich T B₁ α β / (sandwich T B₀ α β + sandwich T B₁ α β) ≤ 1-ε := by
  classical
  let I := {i // i ∈ R.rows}
  let J := {j // j ∈ R.cols}
  letI : Nonempty I := by obtain ⟨i,hi⟩ := R.rows_nonempty; exact ⟨⟨i,hi⟩⟩
  letI : Nonempty J := by obtain ⟨j,hj⟩ := R.cols_nonempty; exact ⟨⟨j,hj⟩⟩
  let T' : Matrix I J ℝ := fun i j => T i j
  let B' (B : Matrix H H ℝ) : Matrix J I ℝ := fun j i => B j i
  have hT' (i : I) (j : J) : 0 < T' i j := R.positive i i.property j j.property
  have hsum (B : Matrix H H ℝ) (hB : ∀ j i, 0 ≤ B j i)
      (hpos : 0 < sandwich T B initial (fun _ => 1)) : 0 < ∑ j : J, ∑ i : I, B' B j i := by
    rw [restrict_sandwich T B R initial (fun _ => 1)] at hpos
    change 0 < ∑ j : J, ∑ i : I,
      (∑ k : I, initial k*T' k j)*B' B j i*(∑ l : J, T' i l*1) at hpos
    have hn (j : J) (i : I) : 0 ≤
        (∑ k : I, initial k*T' k j)*B' B j i*(∑ l : J, T' i l*1) :=
      mul_nonneg (mul_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (hinitial k) (hT' k j).le)
        (hB j i)) (Finset.sum_nonneg fun l _ => mul_nonneg (hT' i l).le (by norm_num))
    obtain ⟨j,_,hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun i _ => hn j i)).mp hpos
    obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hn j i)).mp hj
    have hb : 0 < B' B j i := by
      by_contra hh
      have hz : B' B j i = 0 := le_antisymm (le_of_not_gt hh) (hB j i)
      simp only [hz,mul_zero,zero_mul,lt_self_iff_false] at hi
    have hi' : B' B j i ≤ ∑ i : I, B' B j i :=
      Finset.single_le_sum (f := fun i : I => B' B j i) (fun i _ => hB j i) (Finset.mem_univ i)
    have hj' : (∑ i : I, B' B j i) ≤ ∑ j : J, ∑ i : I, B' B j i :=
      Finset.single_le_sum (f := fun j : J => ∑ i : I, B' B j i)
        (fun j _ => Finset.sum_nonneg fun i _ => hB j i) (Finset.mem_univ j)
    exact hb.trans_le (hi'.trans hj')
  obtain ⟨ε,hε,hcap,hguard⟩ := uniform_posterior_guard T' hT' (B' B₀) (B' B₁)
    (fun j i => hB₀ j i) (fun j i => hB₁ j i) (hsum B₀ hB₀ h₀) (hsum B₁ hB₁ h₁)
  refine ⟨ε,hε,hcap,?_⟩
  intro α β hα hβ htotal
  rw [restrict_sandwich T B₀ R α β,restrict_sandwich T B₁ R α β] at htotal ⊢
  exact hguard (fun i => α i.val) (fun j => β j.val) (fun i => hα i) (fun j => hβ j) htotal

#print axioms supported_message_guard

#print axioms uniform_posterior_guard
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
