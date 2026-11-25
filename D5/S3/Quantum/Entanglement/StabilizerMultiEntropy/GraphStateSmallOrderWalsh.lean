/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateSmallOrderWalsh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Read exact hit masses and their signed cut gap from finite Walsh moments. -/

import Mathlib.Tactic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open Finset
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh.Character
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def char (B U : Finset ι) : ℝ := ∏ i ∈ U, if i ∈ B then -1 else 1

omit [Fintype ι] in
theorem char_eq (B U : Finset ι) : char B U = (-1:ℝ)^(U ∩ B).card := by
  unfold char
  rw [← Finset.prod_filter]
  simp [Finset.filter_mem_eq_inter]

theorem char_compl (B U : Finset ι) : char B Uᶜ = (-1:ℝ)^B.card * char B U := by
  have h : char B U * char B Uᶜ = char B univ := by
    unfold char
    rw [← prod_union disjoint_compl_right, union_compl]
  have hh : char B U * char B U = 1 := by
    rw [char_eq, ← mul_pow]
    norm_num
  calc
    char B Uᶜ = (char B U * char B U) * char B Uᶜ := by rw [hh, one_mul]
    _ = char B univ * char B U := by linear_combination char B U * h
    _ = _ := by rw [char_eq]; simp

theorem char_sum_zero (B : Finset ι) (hB : B.Nonempty) :
    ∑ U : Finset ι, char B U = 0 := by
  obtain ⟨i,hi⟩ := hB
  change ∑ U : Finset ι, (∏ j ∈ U, if j ∈ B then (-1:ℝ) else 1) = 0
  rw [← Finset.powerset_univ, ← Finset.prod_one_add]
  exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh.Character
end

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset
open scoped BigOperators Classical

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def ind (P : Prop) : ℝ := if P then 1 else 0

def side (C T : Finset V) : ℝ := ind (Odd (T ∩ C).card)

def pairs (C T : Finset V) : ℝ := ((T ∩ C).card : ℝ) * ((T ∩ Cᶜ).card : ℝ)

theorem bounds (C T : Finset V) (hT : Even T.card) : side C T ≤ pairs C T := by
  have hcount : (T ∩ C).card + (T ∩ Cᶜ).card = T.card := by
    have h := card_filter_add_card_filter_not (s:=T) (fun i => i ∈ C)
    simpa only [filter_mem_eq_inter, filter_notMem_eq_sdiff, sdiff_eq_inter_compl] using h
  unfold side ind pairs
  by_cases h : Odd (T∩C).card
  · rw [ite_eq_left h]
    have h₁ : 1 ≤ (T∩C).card := h.pos
    have h₂ : 1 ≤ (T∩Cᶜ).card := by
      by_contra! hn
      obtain ⟨a,ha⟩ := h
      obtain ⟨b,hb⟩ := hT
      omega
    exact_mod_cast Nat.mul_le_mul h₁ h₂
  · simp [h]
    positivity

theorem pairs_as_sum (C T : Finset V) :
    pairs C T = ∑ i ∈ C, ∑ j ∈ Cᶜ, ind (i ∈ T) * ind (j ∈ T) := by
  classical
  have he (A : Finset V) : ∑ i ∈ A, ind (i ∈ T) = ((T∩A).card : ℝ) := by
    calc
      _ = ∑ i ∈ A.filter (fun i => i∈T), (1:ℝ) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro i _
        by_cases h : i∈T <;> simp [ind,h]
      _ = _ := by simp [filter_mem_eq_inter,inter_comm]
  unfold pairs
  simp_rw [←mul_sum, ←sum_mul, he]

def expect (μ : Finset V → ℝ) (f : Finset V → ℝ) : ℝ := ∑ T, μ T*f T

/-- Signed parity inequality: only straddling even labels need positive mass. -/
theorem expect_le_pairs (C : Finset V) (μ : Finset V → ℝ)
    (ho : ∀ T, Odd T.card → μ T=0)
    (hsigned : ∀ T, Even T.card → (T∩C).Nonempty → (T∩Cᶜ).Nonempty → 0≤μ T) :
    expect μ (side C) ≤ expect μ (pairs C) := by
  have h : ∀ T, μ T*(side C T) ≤ μ T*(pairs C T) := by
    intro T
    rcases Nat.even_or_odd T.card with he|ho'
    · by_cases hC : (T∩C).Nonempty
      · by_cases hD : (T∩Cᶜ).Nonempty
        · exact mul_le_mul_of_nonneg_left (bounds C T he) (hsigned T he hC hD)
        · have hD' := not_nonempty_iff_eq_empty.mp hD
          have hp0 : pairs C T = 0 := by simp [pairs,hD']
          have hs0 : side C T = 0 := by
            have hb := bounds C T he
            rw [hp0] at hb
            have h₀ : 0≤side C T := by unfold side ind; split <;> norm_num
            exact le_antisymm hb h₀
          simp [hp0,hs0]
      · have hC' := not_nonempty_iff_eq_empty.mp hC
        simp [side,pairs,ind,hC']
    · simp [ho T ho']
  exact sum_le_sum fun T _ => h T

/-- Across any cut, the deterministic parity inequality compares one-bit
parity with the total count of pairs crossing it. For signed measures it is
enough to assume nonnegativity *only on even labels meeting both sides*. -/
theorem signed_gap (C : Finset V) (μ : Finset V → ℝ) (p : ℝ)
    (ho : ∀ T, Odd T.card → μ T=0) (hp : expect μ (side C)=p)
    (hpairs : ∀ i ∈ C, ∀ j ∈ Cᶜ, expect μ (fun T => ind (i∈T)*ind (j∈T))=p^2)
    (hsigned : ∀ T, Even T.card → (T∩C).Nonempty → (T∩Cᶜ).Nonempty → 0≤μ T) :
    p ≤ (C.card : ℝ)*(Cᶜ.card : ℝ)*p^2 := by
  have he := expect_le_pairs C μ ho hsigned
  rw [hp] at he
  have hexp : expect μ (pairs C) = (C.card : ℝ)*(Cᶜ.card : ℝ)*p^2 := by
    unfold expect
    simp_rw [pairs_as_sum, mul_sum]
    rw [sum_comm]
    simp_rw [sum_comm (s:=univ)]
    rw [show (∑ x ∈ C, ∑ x_1 ∈ Cᶜ, ∑ x_2, μ x_2 * (ind (x ∈ x_2) * ind (x_1 ∈ x_2))) =
        ∑ x ∈ C, ∑ x_1 ∈ Cᶜ, p^2 from by
          exact sum_congr rfl fun i hi => sum_congr rfl fun j hj => hpairs i hi j hj]
    simp; ring
  rwa [hexp] at he

theorem exists_negative (C : Finset V) (μ : Finset V → ℝ) (p : ℝ)
    (ho : ∀ T, Odd T.card → μ T=0) (hp : expect μ (side C)=p)
    (hpairs : ∀ i ∈ C, ∀ j ∈ Cᶜ, expect μ (fun T => ind (i∈T)*ind (j∈T))=p^2)
    (hgap : (C.card : ℝ)*(Cᶜ.card : ℝ)*p^2 < p) :
    ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧ μ T<0 := by
  by_contra! hn
  exact hgap.not_ge (signed_gap C μ p ho hp hpairs hn)

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def sign (C T : Finset V) : ℝ := 1-2*side C T
def moment (μ : Finset V → ℝ) (C : Finset V) : ℝ := expect μ (sign C)

omit [DecidableEq V] in
theorem expect_lin (μ : Finset V → ℝ) (a b : ℝ) (f g : Finset V → ℝ) :
    expect μ (fun T => a*f T+b*g T) = a*expect μ f+b*expect μ g := by
  unfold expect
  rw [mul_sum,mul_sum,←sum_add_distrib]
  exact sum_congr rfl fun T _ => by ring

theorem expect_side (μ : Finset V → ℝ) (hμ : ∑ T, μ T=1) (C : Finset V) :
    expect μ (side C) = (1-moment μ C)/2 := by
  have h : moment μ C = expect μ (fun T => 1*(1:ℝ)+(-2)*side C T) := by
    unfold moment
    congr 1
    ext T
    unfold sign
    ring
  rw [h,expect_lin]
  have he : expect μ (fun _ => 1) = 1 := by simpa [expect] using hμ
  rw [he]
  ring

omit [Fintype V] in
theorem singleton_side (i : V) : side {i} = fun T => ind (i∈T) := by
  funext T
  by_cases h : i∈T
  · have he : T∩{i}={i} := by ext z; simp [h]
    simp [side,ind,he,h]
  · have he : T∩{i}=∅ := by ext z; simp [h]
    simp [side,ind,he,h]

omit [Fintype V] in
theorem double_side {i j : V} (hij : i≠j) (T : Finset V) :
    side {i,j} T = ind (i∈T)+ind (j∈T)-2*(ind (i∈T)*ind (j∈T)) := by
  have two : ({i,j} : Finset V).card = 2 := by simp [hij]
  by_cases hi : i∈T <;> by_cases hj : j∈T
  · have he : T∩{i,j}={i,j} := by ext z; simp [eq_comm,hi,hj]
    norm_num [side,ind,he,two,hi,hj]
  · have he : T∩{i,j}={i} := by ext z; simp [eq_comm,hi,hj]
    simp [side,ind,he,hi,hj]
  · have he : T∩{i,j}={j} := by ext z; simp [eq_comm,hi,hj]
    simp [side,ind,he,hi,hj]
  · have he : T∩{i,j}=∅ := by ext z; simp [hi,hj]
    simp [side,ind,he,hi,hj]

theorem pair_moments (μ : Finset V → ℝ) (hμ : ∑ T, μ T=1)
    {i j : V} (hij : i≠j) {x : ℝ} (hi : moment μ {i}=x) (hj : moment μ {j}=x)
    (hij' : moment μ {i,j}=x^2) :
    expect μ (fun T => ind (i∈T)*ind (j∈T))=((1-x)/2)^2 := by
  have hI := expect_side μ hμ {i}
  have hJ := expect_side μ hμ {j}
  have hP := expect_side μ hμ {i,j}
  rw [singleton_side,hi] at hI
  rw [singleton_side,hj] at hJ
  rw [hij'] at hP
  have h : expect μ (side {i,j}) =
      expect μ (fun T => 1*(1*ind (i∈T)+1*ind (j∈T))+(-2)*(ind (i∈T)*ind (j∈T))) := by
    congr 1
    ext T
    rw [double_side hij]
    ring
  rw [h,expect_lin,expect_lin,hI,hJ] at hP
  linarith

omit [Fintype V] in
theorem sign_as_power (C T : Finset V) : sign C T = (-1:ℝ)^(T∩C).card := by
  rcases Nat.even_or_odd (T∩C).card with h|h
  · have hn : ¬Odd (T∩C).card := by
      rintro ⟨a,ha⟩
      obtain ⟨b,hb⟩ := h
      omega
    simp [sign,side,ind,hn,h.neg_pow]
  · norm_num [sign,side,ind,h,h.neg_pow]

theorem moment_gap (C : Finset V) (μ : Finset V → ℝ) (hμ : ∑ T, μ T=1)
    (ho : ∀ T, Odd T.card → μ T=0) {x : ℝ} (hX : x<1)
    (hC : moment μ C=x) (hs : ∀ i, moment μ {i}=x)
    (hp : ∀ i ∈ C, ∀ j ∈ Cᶜ, moment μ {i,j}=x^2)
    (hgap : (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-x)<2) :
    ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧ μ T<0 := by
  have hpos : 0<(1-x)/2 := by linarith
  have hg : (C.card : ℝ)*(Cᶜ.card : ℝ)*((1-x)/2)^2 < (1-x)/2 := by
    have h := mul_lt_mul_of_pos_right hgap hpos
    nlinarith
  apply exists_negative C μ ((1-x)/2) ho _ _ hg
  · rw [expect_side μ hμ,hC]
  · intro i hi j hj
    have hne : i≠j := fun e => (mem_compl.mp hj) (e ▸ hi)
    exact pair_moments μ hμ hne (hs i) (hs j) (hp i hi j hj)

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def walshNorm (V : Type*) [Fintype V] : ℝ := (2:ℝ)^Fintype.card V
def inverse (f : Finset V → ℝ) (T : Finset V) : ℝ := (∑ C, f C*sign C T) / walshNorm V

omit [Fintype V] in
theorem sign_char (C T : Finset V) : sign C T = Character.char C T := by
  rw [sign_as_power,Character.char_eq]

theorem sign_compl (C T : Finset V) : sign Cᶜ T = (-1:ℝ)^T.card*sign C T := by
  have hh (X Y : Finset V) : sign X Y = Character.char Y X := by
    rw [sign_as_power,Character.char_eq,inter_comm]
  rw [hh,Character.char_compl,← hh]

theorem orthog (C D : Finset V) :
    (∑ T : Finset V, sign C T * sign D T) = if C=D then walshNorm V else 0 := by
  simp_rw [sign_char,Character.char,←prod_mul_distrib]
  rw [←Finset.powerset_univ,←Finset.prod_one_add]
  by_cases h : C=D
  · subst D
    rw [ite_eq_left rfl]
    have he (i : V) :
        1+(if i∈C then (-1:ℝ) else 1)*(if i∈C then (-1:ℝ) else 1) = 2 := by
      by_cases hi : i∈C <;> norm_num [hi]
    simp_rw [he]
    simp [walshNorm]
  · rw [ite_eq_right h]
    have hc : ∃ i, (i∈C ∧ i∉D) ∨ (i∉C ∧ i∈D) := by
      by_contra! hh
      apply h
      ext i
      by_cases hi : i∈C <;> by_cases hj : i∈D <;> simp_all
    obtain ⟨i,hi|hi⟩ := hc
    · exact prod_eq_zero (mem_univ i) (by norm_num [hi.1,hi.2])
    · exact prod_eq_zero (mem_univ i) (by norm_num [hi.1,hi.2])

theorem inverse_moment (f : Finset V → ℝ) (D : Finset V) : moment (inverse f) D = f D := by
  unfold moment expect inverse
  have he (T : Finset V) : ((∑ C, f C*sign C T)/walshNorm V)*sign D T =
      (∑ C, f C*sign C T*sign D T)/walshNorm V := by
    calc
      _ = ((∑ C, f C*sign C T)*sign D T)/walshNorm V := by ring
      _ = _ := by rw [sum_mul]
  simp_rw [he]
  rw [←sum_div,sum_comm]
  simp_rw [mul_assoc,←mul_sum,orthog,mul_ite,mul_zero]
  simp [div_eq_mul_inv,show walshNorm V ≠ 0 by unfold walshNorm; positivity]

theorem inverse_mass (f : Finset V → ℝ) (h0 : f ∅ = 1) : ∑ T, inverse f T = 1 := by
  have h := inverse_moment f (∅ : Finset V)
  simpa [moment,expect,sign,side,ind,h0] using h

theorem inverse_odd_zero (f : Finset V → ℝ) (hf : ∀ C, f Cᶜ=f C)
    {T : Finset V} (ho : Odd T.card) : inverse f T=0 := by
  let e : Finset V ≃ Finset V := ⟨compl,compl,compl_compl,compl_compl⟩
  have h := e.sum_comp (fun C => f C*sign C T)
  change (∑ C, f Cᶜ*sign Cᶜ T)=(∑ C, f C*sign C T) at h
  simp only [hf,sign_compl,ho.neg_pow,one_pow,neg_one_mul,mul_neg,sum_neg_distrib] at h
  have hz : ∑ C, f C*sign C T=0 := by linarith
  simp [inverse,hz]

/-- Exact signed Fourier obstruction at a cut. It produces a negative even
frequency meeting both sides, rather than merely refuting a common law. -/
theorem inverse_gap (r : Finset V → ℕ) (C : Finset V)
    (h0 : r ∅=0) (hcompl : ∀ U, r Uᶜ=r U) (hC : r C=1)
    (hS : ∀ i, r {i}=1) (hP : ∀ i∈C, ∀ j∈Cᶜ, r {i,j}=2) (x : ℝ) (hx : x<1)
    (hgap : (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-x)<2) :
    ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧ inverse (fun U => x^r U) T<0 := by
  let g : Finset V → ℝ := fun U => x^r U
  have hmass : ∑ T, inverse g T=1 := inverse_mass g (by simp [g,h0])
  have hodd (T : Finset V) (ho : Odd T.card) : inverse g T=0 :=
    inverse_odd_zero g (by intro U; simp [g,hcompl]) ho
  apply moment_gap C (inverse g) hmass hodd hx _ _ _ hgap
  · rw [inverse_moment]; simp [g,hC]
  · intro i; rw [inverse_moment]; simp [g,hS]
  · intro i hi j hj; rw [inverse_moment]; simp [g,hP i hi j hj]

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem sign_symm (S T : Finset V) : sign S T = sign T S := by
  rw [sign_as_power,sign_as_power,inter_comm]

/-- The moment map on all cuts determines each signed hit mass, not just
existence of a frequency certificate. -/
theorem moment_inverse (μ : Finset V → ℝ) (T : Finset V) :
    inverse (moment μ) T = μ T := by
  unfold inverse moment expect
  simp_rw [sum_mul,mul_assoc]
  rw [sum_comm]
  simp_rw [←mul_sum]
  have h (S : Finset V) : (∑ U : Finset V, sign U S*sign U T) =
      if S=T then walshNorm V else 0 := by
    calc
      _ = ∑ U : Finset V, sign S U*sign T U :=
        sum_congr rfl fun U _ => by rw [(sign_symm U S),(sign_symm U T)]
      _ = _ := orthog S T
  simp_rw [h,mul_ite,mul_zero]
  simp [div_eq_mul_inv,show walshNorm V ≠ 0 by unfold walshNorm; positivity]

def hit (μ : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ T, if Disjoint S T then 0 else μ T

def hitLaw (f : Finset V → ℝ) : Prop :=
  ∃ μ : Finset V → ℝ, (∀ T, 0≤μ T) ∧ (∑ T, μ T=1) ∧
    ∀ S : Finset V, hit μ S=1-(∑ U ∈ S.powerset, f U)/(2:ℝ)^S.card

omit [Fintype V] in
theorem powerset_sign (S T : Finset V) :
    (∑ U ∈ S.powerset, sign U T) = if Disjoint S T then (2:ℝ)^S.card else 0 := by
  have he (U : Finset V) : sign U T = Character.char T U := by rw [sign_symm,sign_char]
  simp_rw [he,Character.char]
  rw [←Finset.prod_one_add]
  by_cases hh : Disjoint S T
  · rw [ite_eq_left hh]
    have h (i : V) (hi : i∈S) : 1+(if i∈T then (-1:ℝ) else 1)=2 := by
      have ht : i∉T := fun ht => (Finset.disjoint_left.mp hh) hi ht
      norm_num [ht]
    exact (prod_congr rfl h).trans (prod_const _)
  · rw [ite_eq_right hh]
    have h : ∃ i∈S, i∈T := by
      by_contra! h'
      exact hh (Finset.disjoint_left.mpr h')
    obtain ⟨i,hi,ht⟩ := h
    exact prod_eq_zero hi (by norm_num [ht])

theorem hit_moment (μ : Finset V → ℝ) (hm : ∑ T, μ T=1) (S : Finset V) :
    hit μ S=1-(∑ U ∈ S.powerset, moment μ U)/(2:ℝ)^S.card := by
  have he : (∑ U ∈ S.powerset, moment μ U) =
      ∑ T, μ T*(if Disjoint S T then (2:ℝ)^S.card else 0) := by
    unfold moment expect
    rw [sum_comm]
    simp_rw [←mul_sum,powerset_sign]
  rw [he,Finset.sum_div,←hm]
  unfold hit
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro T _
  by_cases h : Disjoint S T <;>
    simp [h,show (2:ℝ)^S.card ≠ 0 by positivity]

omit [Fintype V] in
private theorem powerset_inj (f g : Finset V → ℝ)
    (h : ∀ S : Finset V, (∑ U ∈ S.powerset,f U) = ∑ U ∈ S.powerset,g U) : f = g := by
  funext S
  induction S using Finset.strongInduction with
  | H S ih =>
    have hs : S ∈ S.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl _)
    have hh : (∑ U ∈ S.powerset.erase S,f U) = ∑ U ∈ S.powerset.erase S,g U := by
      apply Finset.sum_congr rfl
      intro U hu
      obtain ⟨hne,hsub⟩ := Finset.mem_erase.mp hu
      exact ih U (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hsub,hne⟩)
    have eq := h S
    rw [← Finset.sum_erase_add _ _ hs,← Finset.sum_erase_add _ _ hs,hh] at eq
    exact add_left_cancel eq

theorem hitLaw_iff (f : Finset V → ℝ) (h₀ : f ∅=1) :
    hitLaw f ↔ ∀ T, 0 ≤ inverse f T := by
  constructor
  · rintro ⟨μ,hn,hm,hh⟩ T
    have he : f=moment μ := by
      apply powerset_inj
      intro S
      have h := (hh S).symm.trans (hit_moment μ hm S)
      have hd := sub_right_inj.mp h
      exact (div_left_inj' (show (2:ℝ)^S.card ≠ 0 by positivity)).1 hd
    rw [he,moment_inverse]
    exact hn T
  · intro hn
    refine ⟨inverse f,hn,inverse_mass f h₀,fun S => ?_⟩
    rw [hit_moment (inverse f) (inverse_mass f h₀),show moment (inverse f) = f from funext (inverse_moment f)]

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset Matrix
open scoped BigOperators Classical

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem expect_side_zero (μ : Finset V → ℝ) (hμ : ∑ T, μ T=0) (C : Finset V) :
    expect μ (side C) = -moment μ C/2 := by
  have h : moment μ C = expect μ (fun T => 1*(1:ℝ)+(-2)*side C T) := by
    unfold moment
    congr 1
    exact funext fun T => by unfold sign; ring
  rw [h,expect_lin]
  have he : expect μ (fun _ => 1) = 0 := by simpa [expect] using hμ
  rw [he]
  ring

/-- No differentiation or small-time expansion is needed to detect a
negative XOR rate. The rank-one/rank-two gap forces it by finite cancellation:
one side parity has expectation 1/2, but all crossing pair terms sum to 0. -/
theorem generator_gap (r : Finset V → ℕ) (C : Finset V)
    (h0 : r ∅=0) (hcompl : ∀ U, r Uᶜ=r U) (hC : r C=1)
    (hS : ∀ i, r {i}=1) (hP : ∀ i∈C, ∀ j∈Cᶜ, r {i,j}=2) :
    ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧
      inverse (fun U => -(r U : ℝ)) T<0 := by
  let g : Finset V → ℝ := fun U => -(r U : ℝ)
  let μ := inverse g
  have hμ : ∑ T, μ T=0 := by
    have h := inverse_moment g (∅ : Finset V)
    simpa [moment,expect,sign,side,ind,g,h0,μ] using h
  have hodd (T : Finset V) (ho : Odd T.card) : μ T=0 :=
    inverse_odd_zero g (by intro U; simp [g,hcompl]) ho
  have hside : expect μ (side C)=1/2 := by
    rw [expect_side_zero μ hμ]
    change -moment (inverse g) C/2=_
    rw [inverse_moment]; norm_num [g,hC]
  have hp (i : V) (hi : i∈C) (j : V) (hj : j∈Cᶜ) :
      expect μ (fun T => ind (i∈T)*ind (j∈T))=0 := by
    have e₁ := expect_side_zero μ hμ {i}
    have e₂ := expect_side_zero μ hμ {j}
    have e₃ := expect_side_zero μ hμ {i,j}
    dsimp only [μ] at e₁ e₂ e₃
    rw [inverse_moment,singleton_side] at e₁ e₂
    rw [inverse_moment] at e₃
    simp [g,hS] at e₁ e₂
    simp [g,hP i hi j hj] at e₃
    have hne : i≠j := fun e => (mem_compl.mp hj) (e ▸ hi)
    have he : expect μ (side {i,j}) =
        expect μ (fun T => 1*(1*ind (i∈T)+1*ind (j∈T))+(-2)*(ind (i∈T)*ind (j∈T))) := by
      congr 1
      ext T
      rw [double_side hne]
      ring
    rw [he,expect_lin,expect_lin,e₁,e₂] at e₃
    linarith
  have hsum : expect μ (pairs C)=0 := by
    unfold expect
    simp_rw [pairs_as_sum,mul_sum]
    rw [sum_comm]
    simp_rw [sum_comm (s:=univ)]
    exact sum_eq_zero fun i hi => sum_eq_zero fun j hj => hp i hi j hj
  by_contra! hnonneg
  have he := expect_le_pairs C μ hodd hnonneg
  rw [hside,hsum] at he
  norm_num at he

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Finset Matrix
open scoped BigOperators Classical symmDiff
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem xor_sign (S U T : Finset V) : sign (S ∆ U) T = sign S T * sign U T := by
  simp only [sign_char,Character.char,←Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases hS : i∈S <;> by_cases hU : i∈U <;>
    norm_num [Finset.mem_symmDiff,hS,hU]

def negativeType (g : Finset V → ℝ) : Prop :=
  ∀ a : Finset V → ℝ, (∑ S, a S)=0 →
    (∑ S, ∑ U, a S*a U*g (S ∆ U))≤0

private theorem quadratic_character (g a : Finset V → ℝ) :
    (∑ S, ∑ U, a S*a U*g (S ∆ U)) =
      - ∑ T, inverse (fun S => -g S) T * (∑ S, a S*sign S T)^2 := by
  let μ : Finset V → ℝ := inverse (fun S => -g S)
  have h (S U : Finset V) : g (S ∆ U) = -∑ T, μ T*(sign S T*sign U T) := by
    have h' := inverse_moment (fun S => -g S) (S ∆ U)
    change (∑ T, μ T*sign (S ∆ U) T) = -g (S ∆ U) at h'
    simp_rw [xor_sign] at h'
    linarith
  simp_rw [h,mul_neg,Finset.sum_neg_distrib]
  congr 1
  simp_rw [mul_sum]
  have hs (S : Finset V) :
      (∑ U : Finset V, ∑ T : Finset V, a S*a U*(μ T*(sign S T*sign U T))) =
      ∑ T : Finset V, ∑ U : Finset V, a S*a U*(μ T*(sign S T*sign U T)) := sum_comm
  simp_rw [hs]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro U _
  ring

theorem negative_type_iff_rates (g : Finset V → ℝ) :
    negativeType g ↔ ∀ T : Finset V, T.Nonempty → 0 ≤ inverse (fun S => -g S) T := by
  let μ : Finset V → ℝ := inverse (fun S => -g S)
  constructor
  · intro hn T hT
    let a := fun S => sign T S
    have ha : ∑ S, a S=0 := by
      simp_rw [a,sign_char]
      exact Character.char_sum_zero T hT
    have h := hn a ha
    rw [quadratic_character] at h
    have he (U : Finset V) : (∑ S, a S*sign S U) = if T=U then walshNorm V else 0 := by
      simp_rw [a,fun S => sign_symm S U]
      exact orthog T U
    simp_rw [he,ite_pow,zero_pow (by decide : 2≠0),mul_ite,mul_zero] at h
    have hh : - (μ T * (walshNorm V)^2) ≤ 0 := by simpa [μ,eq_comm] using h
    have hp : 0 < (walshNorm V)^2 := by unfold walshNorm; positivity
    change 0 ≤ μ T
    by_contra! ht
    exact (mul_neg_of_neg_of_pos ht hp).not_ge (neg_nonpos.mp hh)
  · intro hn a ha
    rw [quadratic_character]
    apply neg_nonpos.mpr
    apply sum_nonneg
    intro T _
    by_cases hT : T.Nonempty
    · exact mul_nonneg (hn T hT) (sq_nonneg _)
    · have he : T=∅ := not_nonempty_iff_eq_empty.mp hT
      subst T
      simp [sign,side,ind,ha]

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
