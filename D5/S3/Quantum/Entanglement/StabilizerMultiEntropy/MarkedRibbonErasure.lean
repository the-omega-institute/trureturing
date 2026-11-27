/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal signed ribbon count from one phase-graph deletion instrument, with exact unrecorded erasure cosets. -/
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments

noncomputable section
section

open scoped BigOperators Classical
open Finset
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure

abbrev K := ZMod 2

def sign (x : K) : ℝ := if x = 0 then 1 else -1

theorem sign_zero : sign 0 = 1 := by simp [sign]

theorem sign_mul (x y : K) : sign (x + y) = sign x * sign y := by
  have h : ∀ z : K, z = 0 ∨ z = 1 := by decide
  rcases h x with rfl|rfl <;> rcases h y with rfl|rfl <;>
    simp [sign, show (1:K)+1=0 by decide, show (1:K)≠0 by decide]

theorem add_self_char2 (x : K) : x + x = 0 := by
  fin_cases x <;> decide

theorem sign_sq (x : K) : sign x * sign x = 1 := by
  simp only [sign]
  split <;> norm_num

theorem sign_sum {A : Type*} [AddCommGroup A] [Fintype A] (f : A →+ K) :
    (∑ x, sign (f x)) = if ∀ x, f x = 0 then (Fintype.card A : ℝ) else 0 := by
  classical
  let ψ : AddChar A ℝ :=
    ⟨fun x => sign (f x), by rw [map_zero,sign_zero],
      fun a b => by rw [map_add,sign_mul]⟩
  have hψ : ψ = 0 ↔ ∀ x, f x=0 := by
    constructor
    · intro h x
      have hh := DFunLike.congr_fun h x
      change sign (f x) = 1 at hh
      by_contra hn
      have hs : sign (f x) = -1 := by unfold sign; rw [ite_eq_right hn]
      rw [hs] at hh
      norm_num at hh
    · intro hf
      ext x
      change sign (f x) = 1
      rw [hf x,sign_zero]
  change (∑ x,ψ x) = _
  rw [AddChar.sum_eq_ite]
  by_cases h : ∀ x,f x=0 <;> simp [hψ,h]


theorem ceq (U : Type*) [AddCommGroup U] (f g : U →+ K) :
    (∀ x, (f+g) x = 0) ↔ f = g := by
  constructor
  · intro h
    ext t
    have ht := h t
    simp only [AddMonoidHom.add_apply] at ht
    have he : g t + g t = 0 := add_self_char2 _
    calc f t = f t + (g t + g t) := by rw [he,add_zero]
         _ = g t := by rw [←add_assoc,ht,zero_add]
  · rintro rfl x
    exact add_self_char2 _

variable {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]

/-- Retained left/right coupling P; cross couplings Q/R to erased degrees of
    freedom; erased-to-erased T. The density uses the same full graph for all masks. -/
structure PhaseBlocks (A B C D : Type*) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] where
  P : A →+ B →+ K
  Q : A →+ D →+ K
  R : B →+ C →+ K
  T : C →+ D →+ K

variable (M : PhaseBlocks A B C D)

def total (x : A) (y : B) (c : C) (d : D) : K :=
  M.P x y + M.Q x d + M.R y c + M.T c d

theorem paired_phase (x x' : A) (y y' : B) (c : C) (d : D) :
    sign (total M x y c d) * sign (total M x' y' c d) =
    sign (M.P x y + M.P x' y') * sign ((M.Q x + M.Q x') d) * sign ((M.R y + M.R y') c) := by
  rw [← sign_mul, ← sign_mul, ← sign_mul]
  congr 1
  simp only [total, AddMonoidHom.add_apply]
  have h : M.T c d + M.T c d = 0 := add_self_char2 _
  calc
    _ = M.P x y + M.P x' y' + (M.Q x d + M.Q x' d) + (M.R y c + M.R y' c) +
        (M.T c d + M.T c d) := by abel
    _ = _ := by rw [h,add_zero]

/-- Conditional normalized branch after measuring both erased registers, rescaled
    by sqrt(|A||B|). The exact local Pauli-Z byproducts are visible pointwise. -/
theorem recorded_phase (x : A) (y : B) (c : C) (d : D) :
    sign (total M x y c d) * sign (M.Q x d) * sign (M.R y c) =
      sign (M.P x y) * sign (M.T c d) := by
  simp only [total,sign_mul]
  calc
    _ = sign (M.P x y) * sign (M.T c d) * (sign (M.Q x d) * sign (M.Q x d)) *
        (sign (M.R y c) * sign (M.R y c)) := by ring
    _ = _ := by simp [sign_sq]

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def weight : ℝ := (Fintype.card A : ℝ) * Fintype.card B

def fullWeight : ℝ := weight (A:=A) (B:=B) * ((Fintype.card C : ℝ) * Fintype.card D)

/-- Actual partial trace over erased coordinates of the normalized rank-one
    full phase-state projector; for this real state conjugation is trivial. -/
def erased (x x' : A) (y y' : B) : ℝ :=
  (∑ c : C, ∑ d : D, sign (total M x y c d) * sign (total M x' y' c d)) /
    fullWeight (A:=A) (B:=B) (C:=C) (D:=D)

theorem erased_entry (x x' : A) (y y' : B) :
    erased M x x' y y' =
      if M.Q x = M.Q x' ∧ M.R y = M.R y' then
        sign (M.P x y + M.P x' y') / weight (A:=A) (B:=B) else 0 := by
  classical
  unfold erased
  simp only [paired_phase]
  have hs :
      (∑ c : C, ∑ d : D, sign (M.P x y + M.P x' y') *
          sign ((M.Q x + M.Q x') d) * sign ((M.R y + M.R y') c)) =
      sign (M.P x y + M.P x' y') *
        (∑ d : D, sign ((M.Q x + M.Q x') d)) *
        (∑ c : C, sign ((M.R y + M.R y') c)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Finset.sum_mul,Finset.mul_sum]
  rw [hs,sign_sum,sign_sum]
  simp only [ceq]
  by_cases hq : M.Q x = M.Q x' <;> by_cases hr : M.R y = M.R y' <;> simp [hq,hr]
  have hC : (Fintype.card C : ℝ) ≠ 0 := by positivity
  have hD : (Fintype.card D : ℝ) ≠ 0 := by positivity
  unfold fullWeight
  field_simp

omit [Fintype A] [Fintype B] [Fintype C] [Fintype D] in
/-- Each locally identified pair of loss-syndrome cosets leaves a pure
    phase graph on the homogeneous kernels, up to local signs. -/
theorem coset_phase (x0 x : A) (y0 y : B) :
    sign (M.P (x0+x) (y0+y)) * sign (M.P x y0) * sign (M.P x0 y) =
      sign (M.P x y) * sign (M.P x0 y0) := by
  simp only [map_add,AddMonoidHom.add_apply,sign_mul]
  calc
    _ = sign (M.P x y) * sign (M.P x0 y0) *
        (sign (M.P x y0) * sign (M.P x y0)) *
        (sign (M.P x0 y) * sign (M.P x0 y)) := by ring
    _ = _ := by simp [sign_sq]

/-- Direct pointwise proof of the subnormalized pure blocks inside the actual
    mixed partial trace, with explicit local phase corrections on both sides. -/
theorem erased_coset_corrected (x0 x x' : A) (y0 y y' : B)
    (hx : M.Q x=0) (hx' : M.Q x'=0) (hy : M.R y=0) (hy' : M.R y'=0) :
    erased M (x0+x) (x0+x') (y0+y) (y0+y') *
      (sign (M.P x y0) * sign (M.P x0 y)) *
      (sign (M.P x' y0) * sign (M.P x0 y')) =
      sign (M.P x y + M.P x' y') / weight (A:=A) (B:=B) := by
  have hq : M.Q (x0+x)=M.Q (x0+x') := by simp only [map_add,hx,hx',add_zero]
  have hr : M.R (y0+y)=M.R (y0+y') := by simp only [map_add,hy,hy',add_zero]
  rw [erased_entry, ite_eq_left ⟨hq,hr⟩]
  simp only [sign_mul]
  calc
    _ = (sign (M.P (x0+x) (y0+y)) * sign (M.P x y0) * sign (M.P x0 y)) *
        (sign (M.P (x0+x') (y0+y')) * sign (M.P x' y0) * sign (M.P x0 y')) /
      weight (A:=A) (B:=B) := by ring
    _ = _ := by
      rw [coset_phase,coset_phase]
      rw [show (sign (M.P x y) * sign (M.P x0 y0)) *
          (sign (M.P x' y') * sign (M.P x0 y0)) =
          (sign (M.P x y)*sign (M.P x' y')) *
          (sign (M.P x0 y0)*sign (M.P x0 y0)) by ring,sign_sq,mul_one]

#print axioms erased_coset_corrected

/-- Real marginal of the normalized pure phase graph. The remaining basis
    entries are exactly the fibers of the left-to-right linear map. -/
def left (P : A →+ B →+ K) (x x' : A) : ℝ :=
  (∑ y : B, sign (P x y) * sign (P x' y)) / weight (A:=A) (B:=B)

theorem left_entry (P : A →+ B →+ K) (x x' : A) :
    left P x x' = if P x = P x' then (Fintype.card A : ℝ)⁻¹ else 0 := by
  unfold left weight
  have hg (y : B) : sign (P x y) * sign (P x' y) = sign ((P x + P x') y) := by
    rw [←sign_mul,AddMonoidHom.add_apply]
  simp only [hg,sign_sum,ceq]
  by_cases he : P x=P x'
  · have hb : (Fintype.card B : ℝ) ≠ 0 := by positivity
    have ha : (Fintype.card A : ℝ) ≠ 0 := by positivity
    simp only [he,ite_true]
    field_simp
  · simp [he]

/-- Full cross-coupling erasure annihilates every off-diagonal entry. No
    observer of the unrecorded output can distinguish any retained phase blocks. -/
theorem erasure_forgets_retained (hq : Function.Injective M.Q)
    (hr : Function.Injective M.R) (x x' : A) (y y' : B) :
    erased M x x' y y' =
      if x=x' ∧ y=y' then (weight (A:=A) (B:=B))⁻¹ else 0 := by
  rw [erased_entry]
  by_cases ha : x=x' <;> by_cases hb : y=y'
  · subst x'; subst y'; simp [add_self_char2,sign_zero]
  · simp [ha,hb, show M.R y ≠ M.R y' from fun h => hb (hr h)]
  · simp [ha, show M.Q x ≠ M.Q x' from fun h => ha (hq h)]
  · simp [ha, show M.Q x ≠ M.Q x' from fun h => ha (hq h)]

/-- Exact squared trace of a marginal, without assumptions on the rank of P. -/
theorem left_purity (P : A →+ B →+ K) :
    (∑ x : A, ∑ x' : A, left P x x' * left P x' x) =
      (Fintype.card P.ker : ℝ)/(Fintype.card A : ℝ) := by
  have h (x : A) :
      (∑ x' : A, left P x x' * left P x' x) =
        (Fintype.card P.ker : ℝ)*(Fintype.card A : ℝ)⁻¹^2 := by
    have c (y : A) :
        left P x y * left P y x =
          if P x=P y then (Fintype.card A : ℝ)⁻¹^2 else 0 := by
      rw [left_entry,left_entry]
      by_cases e : P x=P y
      · simp [e,pow_two]
      · simp [e,Ne.symm e]
    have iff' (z : A) : P x = P (x+z) ↔ P z=0 := by
      simp
    simp only [c]
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    change (∑ z : A, if P x=P (x+z) then _ else 0) = _
    simp only [iff']
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    congr 2
    exact (Fintype.card_of_subtype _ (by simp)).symm
  rw [show (∑ x : A, ∑ x' : A, left P x x' * left P x' x) =
      (∑ _ : A, (Fintype.card P.ker : ℝ)*(Fintype.card A : ℝ)⁻¹^2) by simp only [h]]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have ha : (Fintype.card A : ℝ) ≠ 0 := by positivity
  field_simp

#print axioms erasure_forgets_retained
#print axioms left_purity
#print axioms coset_phase
#print axioms left_entry
#print axioms recorded_phase
#print axioms erased_entry
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
end

section

open scoped BigOperators Classical
open Finset LinearMap
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Bits (S : Finset I) := S → K

/-- Zero-extension gives the tensor register split without changing the full graph. -/
def ins (S : Finset I) : Bits S →ₗ[K] (I → K) where
  toFun f i := if hi : i∈S then f ⟨i,hi⟩ else 0
  map_add' f g := by ext i; by_cases hi : i∈S <;> simp [hi]
  map_smul' c f := by ext i; by_cases hi : i∈S <;> simp [hi]

def homOfBilin {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (P : A →ₗ[K] B →ₗ[K] K) : A →+ B →+ K where
  toFun x := (P x).toAddMonoidHom
  map_zero' := by ext x; simp
  map_add' x y := by ext z; simp

def clip (P : LinearMap.BilinForm K (I→K)) (S T : Finset I) :
    Bits S →ₗ[K] Bits T →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => P (ins S x) (ins T y))
    (by intro x y z; simp)
    (by intro r x y; simp)
    (by intro x y z; simp)
    (by intro r x y; simp)

def mask (P : LinearMap.BilinForm K (I→K)) (S : Finset I) :
    PhaseBlocks (Bits S) (Bits S) (Bits Sᶜ) (Bits Sᶜ) where
  P := homOfBilin (clip P S S)
  Q := homOfBilin (clip P S Sᶜ)
  R := homOfBilin (clip P.flip S Sᶜ)
  T := homOfBilin (clip P Sᶜ Sᶜ)

theorem fixed_graph_split (P : LinearMap.BilinForm K (I→K)) (S : Finset I)
    (x y : Bits S) (c d : Bits Sᶜ) :
    total (mask P S) x y c d = P (ins S x + ins Sᶜ c) (ins S y + ins Sᶜ d) := by
  change P (ins S x) (ins S y) + P (ins S x) (ins Sᶜ d) +
    P (ins Sᶜ c) (ins S y) + P (ins Sᶜ c) (ins Sᶜ d) = _
  simp only [map_add,LinearMap.add_apply]
  abel

variable {n : ℕ}

theorem bouquet_clip (a b : I → D n) (t : I → Bool) (S : Finset I) :
    clip (signedBilin a b t) S S =
      signedBilin (fun i:S=>a i) (fun i:S=>b i) (fun i:S=>t i) := by
  ext x y
  -- On coordinate basis elements, zero extension is the corresponding full-bank basis element.
  have h (i : S) : ins S (Pi.single i 1) = Pi.single i.val 1 := by
    funext j
    by_cases hj : j∈S
    · change (if hj' : j∈S then (Pi.single i (1:K) : S→K) ⟨j,hj'⟩ else (0:K)) = _
      simp only [dite_eq_left hj]
      by_cases he : j = i.val
      · subst j; simp
      · have hh : (⟨j,hj⟩ : S) ≠ i := fun H => he (congrArg Subtype.val H)
        simp [Pi.single_eq_of_ne he,Pi.single_eq_of_ne hh]
    · have he : j ≠ i.val := fun H=>hj (H.symm ▸ i.property)
      simp [ins,hj,Pi.single_eq_of_ne he]
  change (clip (signedBilin a b t) S S) (Pi.single x 1) (Pi.single y 1) =
    signedBilin (fun i:S=>a i) (fun i:S=>b i) (fun i:S=>t i) (Pi.single x 1) (Pi.single y 1)
  rw [show (clip (signedBilin a b t) S S) (Pi.single x 1) (Pi.single y 1) =
      signedBilin a b t (ins S (Pi.single x 1)) (ins S (Pi.single y 1)) from rfl]
  rw [h,h,signedBilin_port,signedBilin_port]
  simp only [signedEntry,interlaces,ne_eq,Subtype.coe_inj]
  by_cases hc : (¬y=x) ∧ (between (a y) (b y) (a x) ↔ ¬between (a y) (b y) (b x)) <;>
    by_cases ht : t y=true ∧ x=y <;> simp [hc,ht]

theorem signed_kernel (a b : I → D n) (t : I → Bool) (x : I → K) :
    homOfBilin (signedBilin a b t) x = 0 ↔
      (interlacementMap a b + twistDiagonal t) x = 0 := by
  constructor
  · intro H
    funext i
    have J := DFunLike.congr_fun H (Pi.single i 1)
    change (∑ j, (Pi.single i (1:K) : I→K) j * (interlacementMap a b + twistDiagonal t) x j) = 0 at J
    rw [Finset.sum_eq_single i] at J
    · simpa using J
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  · intro H
    apply AddMonoidHom.ext
    intro y
    change (∑ j, y j * (interlacementMap a b + twistDiagonal t) x j) = 0
    simp [H]

def purity {A B : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup B] [Fintype B]
    (P : A →+ B →+ K) : ℝ := ∑ x : A, ∑ y : A, left P x y * left P y x

theorem signed_purity_rank (a b : I → D n) (t : I → Bool) :
    purity (homOfBilin (signedBilin a b t)) *
      (2:ℝ)^Module.finrank K (interlacementMap a b + twistDiagonal t).range = 1 := by
  unfold purity
  rw [left_purity]
  let L := interlacementMap a b + twistDiagonal t
  have hEq : (homOfBilin (signedBilin a b t)).ker ≃ L.ker :=
    Equiv.subtypeEquivRight (signed_kernel a b t)
  rw [Fintype.card_congr hEq]
  change (Fintype.card L.ker : ℝ) / (Fintype.card (I→K) : ℝ) *
    (2:ℝ)^Module.finrank K L.range = 1
  have h₁ : Fintype.card L.ker = 2^Module.finrank K L.ker := by
    rw [Module.card_eq_pow_finrank (K:=K),ZMod.card]
  have h₂ : Fintype.card (I→K) = 2^Module.finrank K (I→K) := by
    rw [Module.card_eq_pow_finrank (K:=K),ZMod.card]
  rw [h₁,h₂]
  push_cast
  have h := LinearMap.finrank_range_add_finrank_ker L
  change (2:ℝ)^Module.finrank K L.ker / 2^Module.finrank K (I→K) *
    2^Module.finrank K L.range = 1
  rw [←h,add_comm (Module.finrank K L.range),pow_add]
  field_simp

theorem bouquet_boundary_purity (a b : I → D n) (t : I → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ i j, a i≠b j)
    (ho : ∀ i, (a i).val < (b i).val) (S : Finset I) :
    purity (mask (signedBilin a b t) S).P * (2:ℝ)^(1+S.card) =
      (2:ℝ)^(signedBouquetCircleCount a b t S) := by
  change purity (homOfBilin (clip (signedBilin a b t) S S)) * _ = _
  rw [bouquet_clip]
  have h := signed_flag_boundary_plus_rank (fun i:S=>a i) (fun i:S=>b i) (fun i:S=>t i)
    (ha.comp Subtype.val_injective) (hb.comp Subtype.val_injective)
    (fun i j=>hd i j) (fun i=>ho i)
  rw [Fintype.card_coe] at h
  change signedBouquetCircleCount a b t S + _ = _ at h
  rw [←h,pow_add,mul_left_comm,signed_purity_rank,mul_one]

#print axioms fixed_graph_split
#print axioms bouquet_boundary_purity
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
end

section

open Finset
open scoped BigOperators Classical
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure

variable {J : Type*} [Fintype J]
  {A B : J → Type*} [∀ j, AddCommGroup (A j)] [∀ j, AddCommGroup (B j)]

def tensorPhase (P : ∀ j,A j →+ B j →+ K) : (∀ j,A j) →+ (∀ j,B j) →+ K where
  toFun x :=
    { toFun := fun y => ∑ j, P j (x j) (y j)
      map_zero' := by simp
      map_add' := by intro y y'; simp [map_add,sum_add_distrib] }
  map_zero' := by apply AddMonoidHom.ext; intro y; simp
  map_add' := by intro x x'; apply AddMonoidHom.ext; intro y; simp [map_add,sum_add_distrib]

theorem tensorPhase_ker (P : ∀ j,A j →+ B j →+ K) (x : ∀ j,A j) :
    tensorPhase P x=0 ↔ ∀ j,P j (x j)=0 := by
  constructor
  · intro hx j
    apply AddMonoidHom.ext
    intro y
    have H := DFunLike.congr_fun hx (Pi.single j y)
    change (∑ k, (P k (x k)) (Pi.single j y k)) = 0 at H
    rw [sum_eq_single j] at H
    · simpa using H
    · intro k _ hk; simp [Pi.single_eq_of_ne hk]
    · simp
  · intro hx
    apply AddMonoidHom.ext
    intro y
    change (∑ k, P k (x k) (y k)) = 0
    simp [hx]

def tensorKerEquiv (P : ∀ j,A j →+ B j →+ K) :
    (tensorPhase P).ker ≃ ∀ j,(P j).ker where
  toFun x j := ⟨x.val j,(tensorPhase_ker P x.val).mp x.property j⟩
  invFun x := ⟨fun j=>(x j).val,(tensorPhase_ker P _).mpr (fun j=>(x j).property)⟩
  left_inv x := by ext; rfl
  right_inv x := by funext j; exact Subtype.ext rfl

variable [∀ j,Fintype (A j)] [∀ j,Fintype (B j)]

/-- The independent-component literal ribbon readouts are a single
    fixed graph state's tensor-cut purity, not a bank of independently
    varied code marginals. -/
theorem pure_tensor_phase (P : ∀ j,A j →+ B j →+ K) :
    purity (tensorPhase P) = ∏ j,purity (P j) := by
  unfold purity
  simp only [left_purity]
  rw [Fintype.card_congr (tensorKerEquiv P),Fintype.card_pi,Fintype.card_pi]
  push_cast
  rw [Finset.prod_div_distrib]

#print axioms tensorPhase_ker
#print axioms pure_tensor_phase
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
end

section

open scoped BigOperators Classical
open Finset
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
variable {G A : X→X} {m:BandFlag E→X}
    {h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)} {t:E→Bool}

/-- A fixed phase graph for each actual component, before the choice of band mask.
Their tensor product is the full two-register phase graph with zero cross-component edges. -/
def chartForm {j:Components G A m} (C:ChartFibre G A m h0 t j) :=
  signedBilin C.chart.ports.a C.chart.ports.b C.chart.twist

theorem actual_marked_recorded_purity
    (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m) :
    ∃ C : AllCharts G A m h0 t, ∀ s : AllEdges G A m→Bool,
      (∏ j : Components G A m,
        (2:ℝ)^(1+(selected (fun e:EdgeFibre G A m j=>s ⟨j,e⟩)).card) *
          purity (mask (chartForm (C j)) (selected (fun e:EdgeFibre G A m j=>s ⟨j,e⟩))).P) =
      (2:ℝ)^(markedCircleCount G A m t (globalSwitch G A m h0 t C s)) := by
  classical
  let C : AllCharts G A m h0 t := fun j =>
    Classical.choice (exists_fibre_chart (h0:=h0) (t:=t) hG hGf hA hAf hm j)
  refine ⟨C,fun s=>?_⟩
  rw [actual_circles_components G A m hm h0,← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  let S := fun e : EdgeFibre G A m j => s ⟨j,e⟩
  have heq : (fun e:EdgeFibre G A m j=>globalSwitch G A m h0 t C s e.val) =
        switch (C j).state S := by
    funext e
    obtain ⟨e,he⟩ := e
    change edgeComponent G A m e = j at he
    subst j
    rfl
  rw [heq]
  have hr := physical_chart_counts (localGap G A m j) (localCap G A m j)
    (localGap_involution G A m hG j) (localCap_involution G A m hA j)
    (fun x h=>hAf x.val (congrArg Subtype.val h)) (localMark G A m h0 j)
    (localMark_injective G A m hm h0 j) (localCap_mark G A m h0 j)
    (fun e=>t e.val) (C j).state S (C j).chart
  let D := (C j).chart
  rw [hr,mul_comm]
  exact bouquet_boundary_purity D.ports.a D.ports.b D.twist
    D.ports.a_inj D.ports.b_inj D.ports.separate D.ports.ordered (selected S)

/-- The measurement mask rewrites the coordinates of the prebuilt full graph.
    It does not depend on the queried state when defining that graph. -/
theorem actual_full_graph_split (C : AllCharts G A m h0 t) (s : AllEdges G A m→Bool)
    (x y : ∀ j : Components G A m, Bits (selected (fun e : EdgeFibre G A m j => s ⟨j,e⟩)))
    (c d : ∀ j : Components G A m, Bits (selected (fun e : EdgeFibre G A m j => s ⟨j,e⟩))ᶜ) :
    (∑ j, total (mask (chartForm (C j)) (selected (fun e : EdgeFibre G A m j => s ⟨j,e⟩)))
      (x j) (y j) (c j) (d j)) =
    tensorPhase (fun j=>homOfBilin (chartForm (C j)))
      (fun j=>ins (selected (fun e : EdgeFibre G A m j => s ⟨j,e⟩)) (x j) + ins _ (c j))
      (fun j=>ins (selected (fun e : EdgeFibre G A m j => s ⟨j,e⟩)) (y j) + ins _ (d j)) := by
  change _ = ∑ j, chartForm (C j) _ _
  congr 1
  funext j
  exact fixed_graph_split _ _ _ _ _ _

#print axioms actual_full_graph_split
#print axioms actual_marked_recorded_purity
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
end

section OperationalBridge
open scoped BigOperators Classical
open Finset
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure

variable {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- Born mass of the chosen computational-basis outcome in the original
    fixed phase graph. This certifies normalization of every branch. -/
def outcomeMass (M : PhaseBlocks A B C D) (c : C) (d : D) : ℝ :=
  (∑ x : A, ∑ y : B, sign (total M x y c d)*sign (total M x y c d)) /
    fullWeight (A:=A) (B:=B) (C:=C) (D:=D)

theorem outcomeMass_eq (M : PhaseBlocks A B C D) (c : C) (d : D) :
    outcomeMass M c d = (((Fintype.card C : ℝ)*Fintype.card D))⁻¹ := by
  unfold outcomeMass fullWeight weight
  simp only [sign_sq,sum_const,card_univ,nsmul_eq_mul,mul_one]
  have ha : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hb : (Fintype.card B : ℝ) ≠ 0 := by positivity
  have hc : (Fintype.card C : ℝ) ≠ 0 := by positivity
  have hd : (Fintype.card D : ℝ) ≠ 0 := by positivity
  field_simp

#print axioms outcomeMass_eq

/-- The corrected conditional left marginal after the literal computational
    basis measurement. The discarded outcomes are inputs, not implicit in P. -/
def recordedLeft (M : PhaseBlocks A B C D) (c : C) (d : D) (x x' : A) : ℝ :=
  (∑ y : B,
    (sign (total M x y c d) * sign (M.Q x d) * sign (M.R y c)) *
    (sign (total M x' y c d) * sign (M.Q x' d) * sign (M.R y c))) /
  (fullWeight (A:=A) (B:=B) (C:=C) (D:=D)*outcomeMass M c d)

theorem recordedLeft_eq (M : PhaseBlocks A B C D) (c : C) (d : D) (x x' : A) :
    recordedLeft M c d x x' = left M.P x x' := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := by positivity
  have hD : (Fintype.card D : ℝ) ≠ 0 := by positivity
  have hW : fullWeight (A:=A) (B:=B) (C:=C) (D:=D)*outcomeMass M c d =
      weight (A:=A) (B:=B) := by
    rw [outcomeMass_eq,fullWeight]
    field_simp
  unfold recordedLeft left
  rw [hW]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [recorded_phase,recorded_phase]
  calc
    _ = (sign (M.P x y) * sign (M.P x' y)) *
        (sign (M.T c d) * sign (M.T c d)) := by ring
    _ = _ := by rw [sign_sq,mul_one]

def recordedPurity (M : PhaseBlocks A B C D) (c : C) (d : D) : ℝ :=
  ∑ x : A, ∑ x' : A, recordedLeft M c d x x' * recordedLeft M c d x' x

theorem recordedPurity_eq (M : PhaseBlocks A B C D) (c : C) (d : D) :
    recordedPurity M c d = purity M.P := by
  unfold recordedPurity purity
  simp only [recordedLeft_eq]

/-- Actual local outcome-conditioned state of every literal component uses the
    same mask-selected register splitter as the actual unrecorded channel. -/
theorem joint_recorded_actual
    {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {G H : X→X} {m : BandFlag E→X}
    {h0:∀ q,H (m q)=m (q.1,bandCode false false q.2)} {t:E→Bool}
    (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hH:Function.Involutive H) (hHf:∀ x,H x≠x) (hm:Function.Injective m) :
    ∃ C : AllCharts G H m h0 t, ∀ s : AllEdges G H m→Bool,
      ∀ c d : ∀ j : Components G H m, Bits (selected (fun e : EdgeFibre G H m j => s ⟨j,e⟩))ᶜ,
      (∏ j : Components G H m,
        (2:ℝ)^(1+(selected (fun e:EdgeFibre G H m j=>s ⟨j,e⟩)).card) *
          recordedPurity (mask (chartForm (C j)) (selected (fun e:EdgeFibre G H m j=>s ⟨j,e⟩)))
            (c j) (d j)) =
      (2:ℝ)^(markedCircleCount G H m t (globalSwitch G H m h0 t C s)) := by
  obtain ⟨C,HC⟩ := actual_marked_recorded_purity (h0:=h0) (t:=t) hG hGf hH hHf hm
  refine ⟨C,fun s c d=>?_⟩
  simp only [recordedPurity_eq]
  exact HC s

/-- The actual mask on a fixed extracted chart: unrecorded erasure is
    block-diagonal on the actual owner-port syndromes. -/
theorem actual_erasure_entry
    {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {G H : X→X} {m : BandFlag E→X}
    {h0:∀ q,H (m q)=m (q.1,bandCode false false q.2)} {t:E→Bool}
    (C : AllCharts G H m h0 t) (s : AllEdges G H m→Bool) (j : Components G H m)
    (x x' y y' : Bits (selected (fun e : EdgeFibre G H m j => s ⟨j,e⟩))) :
    let M := mask (chartForm (C j)) (selected (fun e : EdgeFibre G H m j => s ⟨j,e⟩))
    erased M x x' y y' =
      if M.Q x = M.Q x' ∧ M.R y = M.R y' then
        sign (M.P x y+M.P x' y') /
          weight (A:=Bits (selected (fun e : EdgeFibre G H m j => s ⟨j,e⟩)))
            (B:=Bits (selected (fun e : EdgeFibre G H m j => s ⟨j,e⟩))) else 0 := by
  dsimp only
  exact erased_entry _ _ _ _ _

/-- Both operations on the very same extracted fixed chart. The equal-syndrome
    case is the subnormalized conditional block of the recordless output. -/
theorem actual_ribbon_two_deletions
    {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {G H : X→X} {m : BandFlag E→X}
    {h0:∀ q,H (m q)=m (q.1,bandCode false false q.2)} {t:E→Bool}
    (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hH:Function.Involutive H) (hHf:∀ x,H x≠x) (hm:Function.Injective m) :
    ∃ C : AllCharts G H m h0 t, ∀ s : AllEdges G H m→Bool,
      let J := Components G H m
      let S := fun j : J => selected (fun e : EdgeFibre G H m j => s ⟨j,e⟩)
      let M := fun j : J => mask (chartForm (C j)) (S j)
      (∀ c d : ∀ j : J, Bits (S j)ᶜ,
        (∏ j : J, (2:ℝ)^(1+(S j).card)*recordedPurity (M j) (c j) (d j)) =
          (2:ℝ)^(markedCircleCount G H m t (globalSwitch G H m h0 t C s))) ∧
      (∀ (j : J) (x x' y y' : Bits (S j)),
        erased (M j) x x' y y' =
          if (M j).Q x = (M j).Q x' ∧ (M j).R y = (M j).R y' then
            sign ((M j).P x y+(M j).P x' y') /
              weight (A:=Bits (S j)) (B:=Bits (S j)) else 0) := by
  obtain ⟨C,HC⟩ := joint_recorded_actual (h0:=h0) (t:=t) hG hGf hH hHf hm
  refine ⟨C, fun s => ?_⟩
  constructor
  · exact HC s
  · intro j x x' y y'
    exact actual_erasure_entry C s j x x' y y'

#print axioms actual_ribbon_two_deletions
#print axioms joint_recorded_actual
#print axioms actual_erasure_entry
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
end OperationalBridge
