/- GID: D5/S3/QuantumContext/RankOfContextualityNonPowerTwo
   generality: I
   mirror-B: D5/B/S3/QuantumContext/RankOfContextualityNonPowerTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quantum behavior has rank of contextuality three. -/

/-
proof_shape: result: content; escape_witness: result
admission_basis: open-problem-resolution (#15370; Proved)
Direct frozen dependencies: the references F0--F4 below are declaration identities; S0--S2 are owner re-pins in this delivery.
Escape audit unfinished for result and JointLaw.push_sum: https://github.com/the-omega-institute/trureturing/issues/15745; DTR-Unregistered.
The result Reg metadata does not decode: contract.cannot_decode:metadata:computation_required; source-bound E1–E8 evidence is missing.
The push_sum Reg metadata fails contract.discovery:rigid_universes; source-bound E1–E8 evidence is missing.
The finite distributions and marginal diagonal argument establish rank three.
The support definitions and consumed helpers reside in this settling module.
The content theorems introduce the generic lower bound, finite parity/cardinality certificates, the marginal obstruction and its cover consequences, and the reindexed Born calculation; the remaining helpers are bind-only with the consumers listed below.
The definitions give the scenario, distributions and matrix construction expressions.
F0: D5/S3/Entropy/Forgetting/CapacityMonotone.pushforward
    sha256:cad2df6e983d5d173955b5b13a616de5ba6ba0334e17112c93d7f2ed629ffbca
F1: D5/S3/Entropy/Forgetting/PushforwardComposition.pushforward_comp
    sha256:656edd11d1bd5231d848d38234fab4d88b8c20381d0741996e70d41b01e756d6
F2: D5/S3/Quantum/FiniteDimensional.QubitMatrix
    sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
F3: D5/S3/Quantum/FiniteDimensional.qubitX
    sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
F4: D5/S3/Quantum/FiniteDimensional.qubitZ
    sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
S0 (same-delivery owner re-pin): D5/S3/QuantumBounds/StatisticalStrengthMagicSquare.square
    sha256:754c699a224cabc64d19c5ea4f68f316677444ee3b0036e8b2ede03a3f62d0d2
S1 (owner re-pin): D5/S3/Entropy/Observation/MultiTargetInformationChain.marginal_pushforward_pair
    sha256:9e730756b3d566a76007798f0a459585083efa4ef7dff728b70e719b5454e43f
S2 (owner re-pin): D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.push_sum
    sha256:ff8b9bdd78e520ec50b11766864e0a2bee95905fe5023c5f74a2d8a819746128
Rows: name | proof_shape | direct frozen dependencies | consumer(s).
Content rows name their own escape witness; bind-only rows have a live consumer.
Behavior | bind-only | none | IsQuantum
restrict | bind-only | none | NonContextual
NonContextual | bind-only | none | Product.chosen
coverSizes | bind-only | none | IsRankOfContextuality
IsRankOfContextuality | bind-only | none | claim
IsQuantum | bind-only | none | claim
claim | bind-only | none | result (type)
push_filter | bind-only | F0 | Product.chosen_spec
sum_joint_first | bind-only | S1 | Product.marginal1_sum
dist_nc | bind-only | F0 | Product.marginal1_nc
Lower.no_two_cover | content; escape_witness=Lower.no_two_cover | none | Product.cover_lower
Square.idx | bind-only | none | Square.C
Square.C | bind-only | none | Matrices.born
Square.parity3 | bind-only | none | Matrices.born_probability
Square.target | bind-only | none | Matrices.born_probability
Square.P | bind-only | none | Matrices.born_probability
Square.bv_xor | bind-only | none | Square.bv_parity
Square.bv_parity | bind-only | none | Square.parity_miss
Square.parity_miss | content; escape_witness=Square.parity_miss | none | Square.contextual
Square.contextual | content; escape_witness=Square.parity_miss | none | Product.marginal1_bad, Product.marginal2_bad
Square.defTarget | bind-only | none | Square.defect_agrees
Square.goodB | bind-only | none | Square.fiber_sum
Square.support | bind-only | none | Square.support_card
Square.support_card | content; escape_witness=Square.support_card | none | Square.mu_mass
Square.mu | bind-only | none | Product.law_agrees
Square.muTable | bind-only | none | Square.fiber_sum
Square.Ndef | bind-only | F0 | Square.defect_agrees
Square.mu_nonneg | bind-only | none | Product.model_nc
Square.mu_mass | bind-only | none | Product.model_nc
Square.fiber_sum | bind-only | none | Square.defect_agrees
Square.fiber_card | content; escape_witness=Square.fiber_card | none | Square.defect_agrees
Square.defect_agrees | content; escape_witness=Square.fiber_card | F0 | Product.law_agrees
Product.C | bind-only | none | Product.O_commute
Product.length_C | bind-only | none | Product.context_get1
Product.decode_encode | bind-only | none | Product.cover_lower
Product.split_restrict | bind-only | none | Product.restrict_eq_iff
Product.restrict_eq_iff | bind-only | none | Product.marginal1_sum
Product.Q | bind-only | none | Product.cover_agrees
Product.p_mass | bind-only | none | Product.marginal1_agrees
Product.productDist | bind-only | none | Product.model
Product.leftG_join | bind-only | none | Product.productDist_factor
Product.rightG_join | bind-only | none | Product.productDist_factor
Product.productDist_mass | bind-only | none | Product.model_nc
Product.productDist_factor | bind-only | F0 | Product.model_agrees
Product.law_agrees | content; escape_witness=Square.defect_agrees | F0 | Product.model_agrees
Product.model | bind-only | F0 | Product.cover
Product.model_nc | bind-only | F0 | Product.cover_nc
Product.model_agrees | content; escape_witness=Product.law_agrees | F0 | Product.cover_agrees
Product.marginal1 | bind-only | F0 | Product.cover_lower
Product.marginal2 | bind-only | F0 | Product.cover_lower
Product.marginal1_nc | bind-only | F0,S2 | Product.marginal1_bad
Product.marginal2_nc | bind-only | F0,S2 | Product.marginal2_bad
Product.marginal1_sum | bind-only | F0,F1 | Product.marginal1_agrees
Product.marginal2_sum | bind-only | F0,F1 | Product.marginal2_agrees
Product.marginal1_agrees | bind-only | F0,F1 | Product.cover_lower
Product.marginal2_agrees | bind-only | F0,F1 | Product.cover_lower
Product.chosen | bind-only | none | Product.chosen_spec
Product.chosen_spec | bind-only | F0 | Product.cover_lower
Product.marginal1_bad | content; escape_witness=Square.contextual | F0 | Product.cover_lower
Product.marginal2_bad | content; escape_witness=Square.contextual | F0 | Product.cover_lower
Product.cover_lower | content; escape_witness=Lower.no_two_cover | F0,F1 | Product.cover_card
Product.third_row | bind-only | none | Product.cover_agrees
Product.cover | bind-only | F0 | Product.cover_agrees
Product.cover_nc | bind-only | F0 | Product.cover_card, Product.rank_three
Product.cover_agrees | content; escape_witness=Product.model_agrees | F0 | Product.cover_card, Product.rank_three
Product.cover_card | content; escape_witness=Product.cover_lower | F0,F1 | Product.rank_three
Product.rank_three | content; escape_witness=Product.cover_lower | F0,F1 | result
Matrices.ZITable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.IZTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.ZZTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.IXTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.XITable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.XXTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.ZXTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.XZTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.YYTable | bind-only | S0,F2,F3,F4 | Matrices.mat_herm_sq
Matrices.obs | bind-only | S0 | Matrices.born
Matrices.mat_herm_sq | bind-only | none | Matrices.obs_herm_sq
Matrices.obs_herm_sq | bind-only | none | Product.O_hermitian_square
Matrices.rho | bind-only | none | Matrices.born
Matrices.born | bind-only | none | Matrices.born_probability
Matrices.born_probability | content; escape_witness=Matrices.born_probability | none | Product.quantum
Matrices.obs_commute | bind-only | none | Product.O_commute
Tensor.tensor | bind-only | none | Product.O
Tensor.tensor_mul | bind-only | none | Product.O_commute
Tensor.tensor_one | bind-only | none | Product.O_hermitian_square
Tensor.tensor_trace | bind-only | none | Product.quantum
Tensor.tensor_hermitian | bind-only | none | Product.O_hermitian_square
Tensor.tensor_smul_left | bind-only | none | Tensor.rho_tensor
Tensor.tensor_smul_right | bind-only | none | Tensor.rho_tensor
Tensor.tensor_add_left | bind-only | none | Tensor.tensor_proj_left
Tensor.tensor_add_right | bind-only | none | Tensor.tensor_proj_right
Tensor.tensor_proj_left | bind-only | none | Product.effect_factor
Tensor.tensor_proj_right | bind-only | none | Product.effect_factor
Tensor.rho | bind-only | none | Product.quantum
Tensor.rho_pos | bind-only | none | Product.quantum
Tensor.rho_trace | bind-only | none | Product.quantum
Tensor.rho_tensor | bind-only | none | Product.quantum
Product.O | bind-only | none | Product.O_commute
Product.O_copy1 | bind-only | none | Product.O_commute
Product.O_copy2 | bind-only | none | Product.O_commute
Product.O_hermitian_square | bind-only | none | Product.quantum
Product.context_get1 | bind-only | none | Product.O_commute
Product.context_get2 | bind-only | none | Product.O_commute
Product.pm_get_idx | bind-only | none | Product.O_commute
Product.O_commute | bind-only | none | Product.quantum
Product.effect | bind-only | none | Product.effect_factor
Product.productEffect | bind-only | none | Product.effect_factor
Product.effect_factor | bind-only | none | Product.quantum
Product.quantum | content; escape_witness=Matrices.born_probability | none | result
result | content; escape_witness=result | F0,F1 | terminal result
-/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw
import D5.S3.Entropy.Forgetting.PushforwardComposition
import D5.S3.Entropy.Observation.MultiTargetInformationChain
import D5.S3.Quantum.FiniteDimensional
import D5.S3.QuantumBounds.StatisticalStrengthMagicSquare

set_option maxHeartbeats 20000000



namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo

open scoped BigOperators ComplexOrder Classical

@[reducible] def Behavior {k m : ℕ} (C : Fin k → List (Fin m)) := (x : Fin k) → (Fin (C x).length → Bool) → ℝ

def restrict {k m : ℕ} (C : Fin k → List (Fin m)) (x : Fin k) (g : Fin m → Bool) : (Fin (C x).length → Bool) :=
  fun i => g ((C x).get i)

def NonContextual {k m : ℕ} (C : Fin k → List (Fin m)) (N : Behavior C) : Prop := by
  classical
  exact ∃ μ : (Fin m → Bool) → ℝ,
    (∀ g, 0 ≤ μ g) ∧
    (∑ g, μ g = 1) ∧
    (∀ x a, N x a = ∑ g with restrict C x g = a, μ g)

def coverSizes {k m : ℕ} (C : Fin k → List (Fin m)) (P : Behavior C) : Set ℕ :=
  {n | ∃ S : Finset (Behavior C), S.card = n ∧
    (∀ N ∈ S, NonContextual C N) ∧
    ∀ x, ∃ N ∈ S, ∀ a, N x a = P x a}

def IsRankOfContextuality {k m : ℕ} (C : Fin k → List (Fin m)) (P : Behavior C) (r : ℕ) : Prop :=
  IsLeast (coverSizes C P) r

def IsQuantum {k m : ℕ} (C : Fin k → List (Fin m)) (P : Behavior C) : Prop :=
  ∃ (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) (O : Fin m → Matrix (Fin d) (Fin d) ℂ),
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
    (∀ v, (O v).IsHermitian ∧ O v * O v = 1) ∧
    (∀ x i j, Commute (O ((C x).get i)) (O ((C x).get j))) ∧
    (∀ x a, (P x a : ℂ) = (ρ * (List.ofFn fun i => (1 / 2 : ℂ) • (1 + (if a i then -1 else 1 : ℂ) • O ((C x).get i))).prod).trace)

def claim : Prop := ∃ (m k : ℕ) (C : Fin k → List (Fin m)) (P : Behavior C) (r : ℕ), IsQuantum C P ∧ IsRankOfContextuality C P r ∧ ∀ n : ℕ, r ≠ 2 ^ n

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
open scoped BigOperators Classical
private lemma push_filter {G H : Type*} [Fintype G] [DecidableEq H]
    (f : G → H) (mu : G → ℝ) (a : H) :
    D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward f mu a = ∑ g with f g = a, mu g := by
  classical
  unfold D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

private lemma sum_joint_first {G A B : Type*} [Fintype G] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : G → A) (r : G → B) (mu : G → ℝ) (a : A) :
    (∑ b, ∑ g with f g = a ∧ r g = b, mu g) =
      ∑ g with f g = a, mu g := by
  classical
  have h := congrFun
    (D5.S3.Entropy.Observation.MultiTargetInformationChain.marginal_pushforward_pair mu f r) a
  convert h using 1 <;>
    simp [D5.S3.Divergence.ChainRule.marginal,
    D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward, Finset.sum_filter,
    Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : f g = a <;> simp [hg]

private lemma dist_nc {k m : ℕ} (C : Fin k → List (Fin m))
    (mu : (Fin m → Bool) → ℝ) (hn : ∀ g, 0 ≤ mu g) (hm : ∑ g, mu g = 1) :
    NonContextual C ((fun x => D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) mu)) := by
  classical
  exact ⟨mu, hn, hm, by intro x a; exact push_filter (restrict C x) mu a⟩

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo

namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Lower

open scoped BigOperators Classical

variable {M I J A B : Type*} [Nonempty I] [Nonempty J]

/-- A generic product-context agreement predicate.  `marg₁` and `marg₂` are the
copy marginals of a model, while `p₁`, `p₂` are the target behaviors. -/
private theorem no_two_cover
    (S : Finset M)
    (marg₁ : M → I → A) (marg₂ : M → J → B)
    (p₁ : I → A) (p₂ : J → B)
    (agree : M → I → J → Prop)
    (hbad₁ : ∀ m ∈ S, ∃ i, marg₁ m i ≠ p₁ i)
    (hbad₂ : ∀ m ∈ S, ∃ j, marg₂ m j ≠ p₂ j)
    (hproj₁ : ∀ m i j, agree m i j → marg₁ m i = p₁ i)
    (hproj₂ : ∀ m i j, agree m i j → marg₂ m j = p₂ j)
    (hcover : ∀ i j, ∃ m ∈ S, agree m i j) :
    3 ≤ S.card := by
  by_contra h
  have hle : S.card ≤ 2 := by omega
  interval_cases hcard : S.card
  · obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨j⟩ := ‹Nonempty J›
    obtain ⟨m, hm, _⟩ := hcover i j
    have : S = ∅ := Finset.card_eq_zero.mp hcard
    simp [this] at hm
  · obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨i, hi⟩ := hbad₁ m (by simpa [hm])
    obtain ⟨j⟩ := ‹Nonempty J›
    obtain ⟨q, hq, haq⟩ := hcover i j
    have hqm : q = m := by simpa [hm] using hq
    subst q
    exact hi (hproj₁ m i j haq)
  · obtain ⟨m, n, hmn, hS⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨i, hi⟩ := hbad₁ m (by simp [hS])
    obtain ⟨j, hj⟩ := hbad₂ n (by simp [hS])
    obtain ⟨q, hq, haq⟩ := hcover i j
    rw [hS] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq
    · subst q; exact hi (hproj₁ _ i j haq)
    · subst q; exact hj (hproj₂ _ i j haq)


end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Lower

set_option maxRecDepth 100000
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000
open scoped BigOperators Classical

def idx (x : Fin 6) (i : Fin 3) : Fin 9 :=
  match x, i with
  | ⟨0,_⟩, ⟨0,_⟩ => 0 | ⟨0,_⟩, ⟨1,_⟩ => 1 | ⟨0,_⟩, ⟨2,_⟩ => 2
  | ⟨1,_⟩, ⟨0,_⟩ => 3 | ⟨1,_⟩, ⟨1,_⟩ => 4 | ⟨1,_⟩, ⟨2,_⟩ => 5
  | ⟨2,_⟩, ⟨0,_⟩ => 6 | ⟨2,_⟩, ⟨1,_⟩ => 7 | ⟨2,_⟩, ⟨2,_⟩ => 8
  | ⟨3,_⟩, ⟨0,_⟩ => 0 | ⟨3,_⟩, ⟨1,_⟩ => 3 | ⟨3,_⟩, ⟨2,_⟩ => 6
  | ⟨4,_⟩, ⟨0,_⟩ => 1 | ⟨4,_⟩, ⟨1,_⟩ => 4 | ⟨4,_⟩, ⟨2,_⟩ => 7
  | ⟨5,_⟩, ⟨0,_⟩ => 2 | ⟨5,_⟩, ⟨1,_⟩ => 5 | ⟨5,_⟩, ⟨2,_⟩ => 8
@[reducible] def C : Fin 6 → List (Fin 9) := fun x => [idx x 0, idx x 1, idx x 2]
def parity3 (a : Fin 3 → Bool) : Bool := xor (xor (a 0) (a 1)) (a 2)
def target (x : Fin 6) : Bool := if x = 5 then true else false
private noncomputable def P (x : Fin 6) (a : Fin 3 → Bool) : ℝ :=
  if parity3 a = target x then 1/4 else 0

private lemma bv_xor (a b : Bool) : Bool.toNat (xor a b) = (Bool.toNat a + Bool.toNat b) % 2 := by cases a <;> cases b <;> rfl
lemma bv_parity (a : Fin 3 → Bool) : Bool.toNat (parity3 a) = (Bool.toNat (a 0) + Bool.toNat (a 1) + Bool.toNat (a 2)) % 2 := by
  have h0 := Bool.toNat_le (a 0); have h1 := Bool.toNat_le (a 1); have h2 := Bool.toNat_le (a 2)
  simp [parity3, bv_xor, Nat.add_mod]
  omega

lemma parity_miss (g : Fin 9 → Bool) : ∃ x, parity3 (fun i => g ((C x).get i)) ≠ target x := by
  by_contra h
  push_neg at h
  let v : Fin 9 → ℕ := fun i => Bool.toNat (g i)
  have hv (i : Fin 9) : v i ≤ 1 := Bool.toNat_le _
  have hvb (i : Fin 9) : (if g i = true then 1 else 0) ≤ 1 := by split <;> omega
  have hx (x : Fin 6) : Bool.toNat (target x) = (v ((C x).get ⟨0, by simp [C]⟩) + v ((C x).get ⟨1, by simp [C]⟩) + v ((C x).get ⟨2, by simp [C]⟩)) % 2 := by
    have hh := congrArg Bool.toNat (h x)
    simpa [C, v, bv_parity] using hh.symm
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
  have h3 := hx 3; have h4 := hx 4; have h5 := hx 5
  have q0 := hvb 0; have q1 := hvb 1; have q2 := hvb 2; have q3 := hvb 3; have q4 := hvb 4
  have q5 := hvb 5; have q6 := hvb 6; have q7 := hvb 7; have q8 := hvb 8
  simp [target, C, idx, v, Bool.toNat] at h0 h1 h2 h3 h4 h5
  omega

private theorem contextual : ¬ ∃ N : Behavior C, NonContextual C N ∧ ∀ x a, N x a = P x a := by
  rintro ⟨N, ⟨μ, hμ, hsum, hrepr⟩, hNP⟩
  have hz (g : Fin 9 → Bool) : μ g = 0 := by
    obtain ⟨x, hx⟩ := parity_miss g
    let a := restrict C x g
    have hPa : P x a = 0 := by
      change (if parity3 (fun i => g ((C x).get i)) = target x then (1/4 : ℝ) else 0) = 0
      rw [if_neg hx]

    have hNa : N x a = 0 := by rw [hNP, hPa]
    have hsum0 : (∑ g' with restrict C x g' = a, μ g') = 0 := by simpa [hrepr x a] using hNa
    have hmem : g ∈ Finset.univ.filter (fun g' => restrict C x g' = a) := by simp [a, restrict]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun g' _ => hμ g')).mp hsum0 g hmem
  have : (∑ g, μ g) = 0 := by simp [hz]
  linarith

private def defTarget (c x : Fin 6) : Bool := xor (target x) (if x = c then true else false)
private def goodB (c : Fin 6) (g : Fin 9 → Bool) : Bool :=
  (BEq.beq (parity3 (fun i => g ((C 0).get i))) (defTarget c 0)) &&
  (BEq.beq (parity3 (fun i => g ((C 1).get i))) (defTarget c 1)) &&
  (BEq.beq (parity3 (fun i => g ((C 2).get i))) (defTarget c 2)) &&
  (BEq.beq (parity3 (fun i => g ((C 3).get i))) (defTarget c 3)) &&
  (BEq.beq (parity3 (fun i => g ((C 4).get i))) (defTarget c 4)) &&
  (BEq.beq (parity3 (fun i => g ((C 5).get i))) (defTarget c 5))
private def support (c : Fin 6) : Finset (Fin 9 → Bool) := Finset.univ.filter (fun g => goodB c g = true)
private lemma support_card (c : Fin 6) : (support c).card = 16 := by fin_cases c <;> decide

private noncomputable def mu (c : Fin 6) (g : Fin 9 → Bool) : ℝ :=
  if goodB c g then (1/16 : ℝ) else 0
private lemma muTable (c : Fin 6) (g : Fin 9 → Bool) :
    mu c g = if goodB c g then (1/16 : ℝ) else 0 := by rfl

private noncomputable def Ndef (c : Fin 6) : Behavior C := fun x => D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) (mu c)
private lemma mu_nonneg (c : Fin 6) (g : Fin 9 → Bool) : 0 ≤ mu c g := by
  unfold mu
  split_ifs <;> norm_num
private lemma mu_mass (c : Fin 6) : (∑ g, mu c g) = 1 := by
  calc
    (∑ g, mu c g) = ∑ _g ∈ support c, (1/16 : ℝ) := by
      simp only [mu, support, Finset.sum_filter]
    _ = 1 := by
      rw [Finset.sum_const, support_card]
      norm_num

private lemma fiber_sum (c x : Fin 6) (a : (Fin (C x).length → Bool)) :
    (∑ g with restrict C x g = a, mu c g) =
      (((support c).filter (fun g => restrict C x g = a)).card : ℝ) * (1/16 : ℝ) := by
  classical
  let s : Finset (Fin 9 → Bool) := Finset.univ.filter (fun g => restrict C x g = a)
  change Finset.sum s (mu c) = _
  have hsum0 : Finset.sum s (mu c) =
      Finset.sum (s.filter (fun g => goodB c g = true)) (fun _ => (1/16 : ℝ)) := by
    calc
      Finset.sum s (mu c) = Finset.sum s (fun g => if goodB c g = true then (1/16 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact muTable c g
      _ = Finset.sum (s.filter (fun g => goodB c g = true)) (fun _ => (1/16 : ℝ)) := by
        simpa only [Finset.sum_filter]
  have hset : s.filter (fun g => goodB c g = true) =
      (support c).filter (fun g => restrict C x g = a) := by
    ext g
    simp [s, support, and_comm]
  rw [hsum0, hset, Finset.sum_const]
  simp [nsmul_eq_mul]


end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square
set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

private lemma fiber_card (c x : Fin 6) (a : (Fin (C x).length → Bool)) :
    ((support c).filter (fun g => restrict C x g = a)).card =
      if parity3 (fun i => a ⟨i, by simp [C]⟩) = defTarget c x then 4 else 0 := by
  change Fin 3 → Bool at a
  fin_cases c <;> fin_cases x
  all_goals
    have ha : a = ![a 0, a 1, a 2] := by ext i; fin_cases i <;> rfl
    rw [ha]
    generalize a 0 = b0
    generalize a 1 = b1
    generalize a 2 = b2
    cases b0 <;> cases b1 <;> cases b2 <;> decide

private lemma defect_agrees (c x : Fin 6) (h : x ≠ c) (a : (Fin (C x).length → Bool)) :
    Ndef c x a = P x a := by
  simp only [Ndef, push_filter]
  rw [fiber_sum c x a, fiber_card c x a]
  simp only [defTarget, if_neg h, Bool.xor_false]
  unfold P
  have ha : (fun i : Fin 3 => a ⟨i.val, by simp [C]⟩) = a := by
    funext i
    apply congrArg a
    apply Fin.ext
    rfl
  rw [ha]
  split <;> norm_num

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
open scoped BigOperators Classical

@[reducible] private def C (x : Fin 36) : List (Fin 18) :=
  (Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1).map (Fin.castAdd 9) ++ (Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2).map (Fin.natAdd 9)
private lemma length_C (x : Fin 36) : (C x).length = 6 := by simp [C, Square.C]
private lemma decode_encode (s t : Fin 6) : ((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) ((fun (s t : Fin 6) => finProdFinEquiv (s,t)) s t) = (s,t) := by simp []

private lemma split_restrict (x : Fin 36) (g : Fin 18 → Bool) :
    (fun (_x : Fin 36) => (Fin.appendEquiv (α := Bool) 3 3).symm) x (restrict C x g) =
      ((restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) g)), (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) g))) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
private lemma restrict_eq_iff (x : Fin 36) (g : Fin 18 → Bool) (a : (Fin (C x).length → Bool)) :
    restrict C x g = a ↔
      (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) g)) = (((Fin.appendEquiv (α := Bool) 3 3).symm a).1) ∧
      (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) g)) = (((Fin.appendEquiv (α := Bool) 3 3).symm a).2) := by
  change Fin 6 → Bool at a
  rw [← ((fun (_x : Fin 36) => (Fin.appendEquiv (α := Bool) 3 3).symm) x).injective.eq_iff, split_restrict]
  change ((restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) g)), (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) g))) =
    ((((Fin.appendEquiv (α := Bool) 3 3).symm a).1),(((Fin.appendEquiv (α := Bool) 3 3).symm a).2)) ↔ _
  simp only [Prod.mk.injEq]

private noncomputable def Q : Behavior C :=
  fun x a => Square.P (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).1)) * Square.P (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).2))

private lemma p_mass (x : Fin 6) : (∑ a : Fin 3 → Bool, Square.P x a) = 1 := by
  classical
  have hc : (Finset.univ.filter (fun a : Fin 3 → Bool => Square.parity3 a = Square.target x)).card = 4 := by
    fin_cases x <;> decide
  change (∑ a : Fin 3 → Bool, if Square.parity3 a = Square.target x then (1/4 : ℝ) else 0) = 1
  rw [← Finset.sum_filter, Finset.sum_const, hc]
  norm_num

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
set_option maxRecDepth 100000
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
open scoped BigOperators Classical
private noncomputable def productDist (mu nu : (Fin 9 → Bool) → ℝ) (g : Fin 18 → Bool) : ℝ :=
  Matrix.vecMulVec mu nu (fun i => g (Fin.castAdd 9 i)) (fun i => g (Fin.natAdd 9 i))
private lemma leftG_join (a b : Fin 9 → Bool) : (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) (((Fin.appendEquiv (α := Bool) 9 9).symm).symm (a,b)) = a := by
  change (((Fin.appendEquiv (α := Bool) 9 9).symm) (((Fin.appendEquiv (α := Bool) 9 9).symm).symm (a,b))).1 = a
  simp
private lemma rightG_join (a b : Fin 9 → Bool) : (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) (((Fin.appendEquiv (α := Bool) 9 9).symm).symm (a,b)) = b := by
  change (((Fin.appendEquiv (α := Bool) 9 9).symm) (((Fin.appendEquiv (α := Bool) 9 9).symm).symm (a,b))).2 = b
  simp
private lemma productDist_mass (mu nu : (Fin 9 → Bool) → ℝ)
    (hm : ∑ g, mu g = 1) (hn : ∑ g, nu g = 1) :
    (∑ g, productDist mu nu g) = 1 := by
  classical
  rw [← ((Fin.appendEquiv (α := Bool) 9 9).symm).symm.sum_comp]
  simp only [productDist, Matrix.vecMulVec_apply, leftG_join, rightG_join, Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum, hm, hn, one_mul]

private lemma productDist_factor (mu nu : (Fin 9 → Bool) → ℝ) (x : Fin 36) (a : (Fin (C x).length → Bool)) :
    (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) (productDist mu nu)) a =
      (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1) mu) ((((Fin.appendEquiv (α := Bool) 3 3).symm a).1)) * (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2) nu) ((((Fin.appendEquiv (α := Bool) 3 3).symm a).2)) := by
  classical
  simp only [push_filter]
  simp only [Finset.sum_filter]
  rw [← ((Fin.appendEquiv (α := Bool) 9 9).symm).symm.sum_comp]
  simp only [Fintype.sum_prod_type, restrict_eq_iff, productDist, Matrix.vecMulVec_apply, leftG_join, rightG_join]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp_all

private lemma law_agrees (c s : Fin 6) (hs : s ≠ c) (a : Fin 3 → Bool) :
    (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C s) (Square.mu c)) a = Square.P s a := by
  have ha : (fun i : Fin 3 =>
      a (⟨i.val,by simpa [Square.C] using i.isLt⟩ : Fin (Square.C s).length)) = a := by
    funext i
    apply congrArg a
    apply Fin.ext
    rfl
  simpa only [Square.Ndef,Square.P,ha] using Square.defect_agrees c s hs a

private noncomputable def model (c : Fin 6) : Behavior C :=
  (fun x => D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) (productDist (Square.mu c) (Square.mu c)))
private lemma model_nc (c : Fin 6) : NonContextual C (model c) := by
  apply dist_nc
  · intro g
    exact mul_nonneg (Square.mu_nonneg c _) (Square.mu_nonneg c _)
  · exact productDist_mass _ _ (Square.mu_mass c) (Square.mu_mass c)
private lemma model_agrees (c : Fin 6) (x : Fin 36)
    (h1 : (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ≠ c) (h2 : (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ≠ c) :
    ∀ a, model c x a = Q x a := by
  intro a
  rw [model, productDist_factor, law_agrees c _ h1, law_agrees c _ h2]
  rfl

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
set_option maxRecDepth 100000
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
open scoped BigOperators Classical
private noncomputable def marginal1 (mu : (Fin 18 → Bool) → ℝ) : Behavior Square.C :=
  (fun x => D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C x) (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) mu))
private noncomputable def marginal2 (mu : (Fin 18 → Bool) → ℝ) : Behavior Square.C :=
  (fun x => D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C x) (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) mu))
private lemma marginal1_nc (mu : (Fin 18 → Bool) → ℝ) (hn : ∀ g, 0 ≤ mu g) (hm : ∑ g, mu g = 1) :
    NonContextual Square.C (marginal1 mu) := by
  apply dist_nc
  · intro a
    unfold D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward
    exact Finset.sum_nonneg fun g _ => by
      split_ifs <;> simp_all only [le_refl, hn]
  · rw [D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw.push_sum]; exact hm
private lemma marginal2_nc (mu : (Fin 18 → Bool) → ℝ) (hn : ∀ g, 0 ≤ mu g) (hm : ∑ g, mu g = 1) :
    NonContextual Square.C (marginal2 mu) := by
  apply dist_nc
  · intro a
    unfold D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward
    exact Finset.sum_nonneg fun g _ => by
      split_ifs <;> simp_all only [le_refl, hn]
  · rw [D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw.push_sum]; exact hm
private lemma marginal1_sum (mu : (Fin 18 → Bool) → ℝ) (x : Fin 36) (a : Fin 3 → Bool) :
    marginal1 mu (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 a =
      ∑ b : Fin 3 → Bool, (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) mu) (((Fin.appendEquiv (α := Bool) 3 3) (a,b))) := by
  classical
  change (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1) (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) mu)) a = _
  rw [congrFun (D5.S3.Entropy.Forgetting.PushforwardComposition.pushforward_comp mu (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1)) a]
  simp only [push_filter, Function.comp_apply]
  simp only [restrict_eq_iff, Equiv.symm_apply_apply]
  exact (sum_joint_first (fun g => (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.castAdd 9 i)) g)))
    (fun g => (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) g))) mu a).symm
private lemma marginal2_sum (mu : (Fin 18 → Bool) → ℝ) (x : Fin 36) (b : Fin 3 → Bool) :
    marginal2 mu (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 b =
      ∑ a : Fin 3 → Bool, (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) mu) (((Fin.appendEquiv (α := Bool) 3 3) (a,b))) := by
  classical
  change (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2) (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) mu)) b = _
  rw [congrFun (D5.S3.Entropy.Forgetting.PushforwardComposition.pushforward_comp mu (fun (g : Fin 18 → Bool) (i : Fin 9) => g (Fin.natAdd 9 i)) (restrict Square.C (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2)) b]
  simp only [push_filter, Function.comp_apply]
  simp only [restrict_eq_iff, Equiv.symm_apply_apply]
  symm
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : restrict Square.C
      (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2
      (fun i => g (Fin.natAdd 9 i)) = b <;> simp_all


private lemma marginal1_agrees (mu : (Fin 18 → Bool) → ℝ) (x : Fin 36)
    (h : ∀ a, (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) mu) a = Q x a) :
    marginal1 mu (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 = Square.P (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 := by
  funext a
  change Fin 3 → Bool at a
  rw [marginal1_sum]
  simp_rw [h, Q, Equiv.symm_apply_apply]
  rw [← Finset.mul_sum, p_mass, mul_one]
private lemma marginal2_agrees (mu : (Fin 18 → Bool) → ℝ) (x : Fin 36)
    (h : ∀ a, (D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) mu) a = Q x a) :
    marginal2 mu (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 = Square.P (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 := by
  funext b
  change Fin 3 → Bool at b
  rw [marginal2_sum]
  simp_rw [h, Q, Equiv.symm_apply_apply]
  rw [← Finset.sum_mul, p_mass, one_mul]

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
set_option maxRecDepth 100000
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
open scoped BigOperators Classical
private noncomputable def chosen (N : Behavior C) : (Fin 18 → Bool) → ℝ := by
  classical
  exact if h : NonContextual C N then h.choose else fun _ => 0
private lemma chosen_spec (N : Behavior C) (h : NonContextual C N) :
    (∀ g, 0 ≤ chosen N g) ∧ (∑ g, chosen N g = 1) ∧
      N = (fun x => D5.S3.Entropy.Forgetting.CapacityMonotone.pushforward (restrict C x) (chosen N)) := by
  classical
  unfold chosen
  rw [dif_pos h]
  obtain ⟨hn,hm,hr⟩ := h.choose_spec
  exact ⟨hn,hm,by funext x a; exact (hr x a).trans (push_filter (restrict C x) h.choose a).symm⟩

private lemma marginal1_bad (mu : (Fin 18 → Bool) → ℝ) (hn : ∀ g, 0 ≤ mu g) (hm : ∑ g, mu g = 1) :
    ∃ s, marginal1 mu s ≠ Square.P s := by
  classical
  by_contra h
  push_neg at h
  apply Square.contextual
  exact ⟨marginal1 mu,marginal1_nc mu hn hm,fun s a => congrFun (h s) a⟩
private lemma marginal2_bad (mu : (Fin 18 → Bool) → ℝ) (hn : ∀ g, 0 ≤ mu g) (hm : ∑ g, mu g = 1) :
    ∃ s, marginal2 mu s ≠ Square.P s := by
  classical
  by_contra h
  push_neg at h
  apply Square.contextual
  exact ⟨marginal2 mu,marginal2_nc mu hn hm,fun s a => congrFun (h s) a⟩

private theorem cover_lower (S : Finset (Behavior C))
    (hNC : ∀ N ∈ S, NonContextual C N)
    (hcover : ∀ x, ∃ N ∈ S, ∀ a, N x a = Q x a) : 3 ≤ S.card := by
  classical
  apply Lower.no_two_cover S
    (fun N s => marginal1 (chosen N) s = Square.P s)
    (fun N t => marginal2 (chosen N) t = Square.P t)
    (fun _ => True) (fun _ => True)
    (fun N s t => NonContextual C N ∧ ∀ a, N ((fun (s t : Fin 6) => finProdFinEquiv (s,t)) s t) a = Q ((fun (s t : Fin 6) => finProdFinEquiv (s,t)) s t) a)
  · intro N hN
    obtain ⟨hn,hm,_⟩ := chosen_spec N (hNC N hN)
    obtain ⟨s,hs⟩ := marginal1_bad _ hn hm
    exact ⟨s,fun h => hs (h.symm ▸ True.intro)⟩
  · intro N hN
    obtain ⟨hn,hm,_⟩ := chosen_spec N (hNC N hN)
    obtain ⟨t,ht⟩ := marginal2_bad _ hn hm
    exact ⟨t,fun h => ht (h.symm ▸ True.intro)⟩
  · intro N s t h
    have hr := (chosen_spec N h.1).2.2
    have h' := marginal1_agrees (chosen N) ((fun (s t : Fin 6) => finProdFinEquiv (s,t)) s t) (by intro a; exact (congrFun (congrFun hr _) a).symm.trans (h.2 a))
    have hp : marginal1 (chosen N) s = Square.P s :=
      Eq.mp (congrArg (fun st : Fin 6 × Fin 6 => marginal1 (chosen N) st.1 = Square.P st.1)
        (decode_encode s t)) h'
    exact propext ⟨fun _ => True.intro,fun _ => hp⟩
  · intro N s t h
    have hr := (chosen_spec N h.1).2.2
    have h' := marginal2_agrees (chosen N) ((fun (s t : Fin 6) => finProdFinEquiv (s,t)) s t) (by intro a; exact (congrFun (congrFun hr _) a).symm.trans (h.2 a))
    have hp : marginal2 (chosen N) t = Square.P t :=
      Eq.mp (congrArg (fun st : Fin 6 × Fin 6 => marginal2 (chosen N) st.2 = Square.P st.2)
        (decode_encode s t)) h'
    exact propext ⟨fun _ => True.intro,fun _ => hp⟩
  · intro s t
    obtain ⟨N,hN,ha⟩ := hcover ((fun (s t : Fin 6) => finProdFinEquiv (s,t)) s t)
    exact ⟨N,hN,hNC N hN,ha⟩

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
open scoped BigOperators Classical

private lemma third_row (s t : Fin 6) : ∃ c : Fin 3, s ≠ (Fin.castLE (by decide : 3 ≤ 6)) c ∧ t ≠ (Fin.castLE (by decide : 3 ≤ 6)) c := by
  fin_cases s <;> fin_cases t <;> decide

private noncomputable def cover : Finset (Behavior C) := by
  classical
  exact Finset.univ.image (fun c : Fin 3 => model ((Fin.castLE (by decide : 3 ≤ 6)) c))
private lemma cover_nc : ∀ N ∈ cover, NonContextual C N := by
  classical
  intro N hN
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hN
  exact model_nc _
private lemma cover_agrees : ∀ x, ∃ N ∈ cover, ∀ a, N x a = Q x a := by
  classical
  intro x
  obtain ⟨c,hc1,hc2⟩ := third_row (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2
  exact ⟨model ((Fin.castLE (by decide : 3 ≤ 6)) c), Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩,model_agrees _ _ hc1 hc2⟩
private lemma cover_card : cover.card = 3 := by
  classical
  have hlo := cover_lower cover cover_nc cover_agrees
  have hhi : cover.card ≤ 3 := by
    exact le_trans (Finset.card_image_le) (by simp)
  omega

private theorem rank_three : IsRankOfContextuality C Q 3 := by
  classical
  constructor
  · exact ⟨cover,cover_card,cover_nc,cover_agrees⟩
  · intro n hn
    obtain ⟨S,hcard,hNC,hcover⟩ := hn
    rw [← hcard]
    exact cover_lower S hNC hcover

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
set_option maxHeartbeats 10000000
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices

noncomputable def obs : Fin 9 → Matrix (Fin 4) (Fin 4) ℂ := fun v =>
  let rc := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3)).symm) v
  (D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square rc.1 rc.2).submatrix
    ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).symm)
    ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).symm)

lemma ZITable : obs 0 = !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma IZTable : obs 1 = !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma ZZTable : obs 2 = !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma IXTable : obs 3 = !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

lemma XITable : obs 4 = !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma XXTable : obs 5 = !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma ZXTable : obs 6 = !![0,1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,-1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma XZTable : obs 7 = !![0,0,1,0; 0,0,0,-1; 1,0,0,0; 0,-1,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma YYTable : obs 8 = !![0,0,0,-1; 0,0,1,0; 0,1,0,0; -1,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.square,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.submatrix, finProdFinEquiv,
      Matrix.one_apply, Fin.divNat, Fin.modNat, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma mat_herm_sq (A : Matrix (Fin 4) (Fin 4) ℂ)
    (h : A = obs 0 ∨ A = obs 1 ∨ A = obs 2 ∨ A = obs 3 ∨ A = obs 4 ∨
      A = obs 5 ∨ A = obs 6 ∨ A = obs 7 ∨ A = obs 8) :
    A.IsHermitian ∧ A * A = 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor
  all_goals
    first
    | (rw [Matrix.IsHermitian]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [ZITable, IZTable, ZZTable, IXTable, XITable, XXTable, ZXTable, XZTable, YYTable])
    | (ext i j; fin_cases i <;> fin_cases j <;>
        simp [ZITable, IZTable, ZZTable, IXTable, XITable, XXTable, ZXTable, XZTable, YYTable,
          Matrix.mul_apply, Fin.sum_univ_succ])

lemma obs_herm_sq : ∀ v, (obs v).IsHermitian ∧ obs v * obs v = 1 := by
  intro v
  fin_cases v <;> apply mat_herm_sq <;> simp

private noncomputable def rho : Matrix (Fin 4) (Fin 4) ℂ := (1/4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

private noncomputable def born (x : Fin 6) (a : Fin 3 → Bool) : ℂ :=
  (rho * (List.ofFn fun i => (1 / 2 : ℂ) •
    (1 + (if a i then -1 else 1 : ℂ) • obs ((Square.C x).get i))).prod).trace

private lemma born_probability : ∀ x a, (Square.P x a : ℂ) = born x a := by
  intro x a
  generalize h0 : a 0 = b0
  generalize h1 : a 1 = b1
  generalize h2 : a 2 = b2
  cases b0 <;> cases b1 <;> cases b2 <;> fin_cases x <;>
    simp [Square.P, Square.parity3, Square.target, born, rho, Square.C, Square.idx,
      ZITable, IZTable, ZZTable, IXTable, XITable, XXTable, ZXTable, XZTable, YYTable,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, Fin.foldr_succ, Fin.foldr_zero,
      List.ofFn, List.prod_cons, List.prod_nil, h0, h1, h2] <;>
    norm_num


private lemma obs_commute : ∀ x i j, Commute (obs ((Square.C x).get i)) (obs ((Square.C x).get j)) := by
  intro x i j
  fin_cases x <;> fin_cases i <;> fin_cases j
  all_goals
    (rw [commute_iff_eq] <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Square.C, Square.idx,
        ZITable, IZTable, ZZTable, IXTable, XITable, XXTable, ZXTable, XZTable, YYTable,
        Matrix.mul_apply, Fin.sum_univ_succ])


end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Tensor
open scoped ComplexOrder BigOperators
private def tensor (A B : (Matrix (Fin 4) (Fin 4) ℂ)) : (Matrix (Fin 16) (Fin 16) ℂ) :=
  (Matrix.kroneckerMap (fun x y : ℂ => x*y) A B).submatrix ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin (4*4)).symm) ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin (4*4)).symm)
private lemma tensor_mul (A B A' B' : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor A B * tensor A' B' = tensor (A * A') (B * B') := by
  unfold tensor
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
private lemma tensor_one : tensor 1 1 = 1 := by
  unfold tensor
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin (4*4)).symm)
private lemma tensor_trace (A B : (Matrix (Fin 4) (Fin 4) ℂ)) : (tensor A B).trace = A.trace * B.trace := by
  unfold tensor Matrix.trace
  change (∑ i : Fin 16, Matrix.diag (Matrix.kroneckerMap (fun x y : ℂ => x*y) A B) (((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin (4*4)).symm) i)) = _
  rw [((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin (4*4)).symm).sum_comp]
  exact Matrix.trace_kronecker A B
private lemma tensor_hermitian (A B : (Matrix (Fin 4) (Fin 4) ℂ)) (ha : A.IsHermitian) (hb : B.IsHermitian) :
    (tensor A B).IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, ha, hb]
private lemma tensor_smul_left (s : ℂ) (A B : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor (s • A) B = s • tensor A B := by
  unfold tensor
  rw [Matrix.smul_kronecker, Matrix.submatrix_smul]; rfl
private lemma tensor_smul_right (s : ℂ) (A B : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor A (s • B) = s • tensor A B := by
  unfold tensor
  rw [Matrix.kronecker_smul, Matrix.submatrix_smul]; rfl
private lemma tensor_add_left (A B D : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor (A+B) D = tensor A D + tensor B D := by
  unfold tensor
  rw [Matrix.add_kronecker, Matrix.submatrix_add]; rfl
private lemma tensor_add_right (A B D : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor A (B+D) = tensor A B + tensor A D := by
  unfold tensor
  rw [Matrix.kronecker_add, Matrix.submatrix_add]; rfl
private lemma tensor_proj_left (s : ℂ) (A : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor ((1/2 : ℂ) • (1+s•A)) 1 = (1/2 : ℂ) • (1+s•tensor A 1) := by
  rw [tensor_smul_left, tensor_add_left, tensor_smul_left, tensor_one]
private lemma tensor_proj_right (s : ℂ) (A : (Matrix (Fin 4) (Fin 4) ℂ)) :
    tensor 1 ((1/2 : ℂ) • (1+s•A)) = (1/2 : ℂ) • (1+s•tensor 1 A) := by
  rw [tensor_smul_right, tensor_add_right, tensor_smul_right, tensor_one]

private noncomputable def rho : (Matrix (Fin 16) (Fin 16) ℂ) := (1/16 : ℂ) • 1
private lemma rho_pos : rho.PosSemidef := by
  apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
  norm_num [Complex.nonneg_iff]
private lemma rho_trace : rho.trace = 1 := by norm_num [rho,Matrix.trace_smul,Matrix.trace_one]
private lemma rho_tensor : tensor ((1/4 : ℂ) • 1) ((1/4 : ℂ) • 1) = rho := by
  rw [tensor_smul_left,tensor_smul_right,tensor_one,smul_smul]
  norm_num [rho]

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Tensor
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
open Tensor
open scoped ComplexOrder

private noncomputable def O : Fin 18 → (Matrix (Fin 16) (Fin 16) ℂ) := Fin.append (fun v => tensor (Matrices.obs v) 1) (fun v => tensor 1 (Matrices.obs v))
private lemma O_copy1 (v : Fin 9) : O ((Fin.castAdd 9) v) = tensor (Matrices.obs v) 1 := by
  exact Fin.append_left _ _ v
private lemma O_copy2 (v : Fin 9) : O ((Fin.natAdd 9) v) = tensor 1 (Matrices.obs v) := by
  exact Fin.append_right _ _ v
private lemma O_hermitian_square (v : Fin 18) : (O v).IsHermitian ∧ O v * O v = 1 := by
  refine Fin.addCases (m:=9) (n:=9) ?_ ?_ v
  · intro u
    rw [show Fin.castAdd 9 u = (Fin.castAdd 9) u by rfl, O_copy1]
    obtain ⟨hh,hs⟩ := Matrices.obs_herm_sq u
    exact ⟨tensor_hermitian _ _ hh Matrix.isHermitian_one, by rw [tensor_mul,hs,one_mul,tensor_one]⟩
  · intro u
    rw [show Fin.natAdd 9 u = (Fin.natAdd 9) u by rfl, O_copy2]
    obtain ⟨hh,hs⟩ := Matrices.obs_herm_sq u
    exact ⟨tensor_hermitian _ _ Matrix.isHermitian_one hh, by rw [tensor_mul,hs,one_mul,tensor_one]⟩

private lemma context_get1 (x : Fin 36) (i : Fin 3) :
    (C x).get ⟨i, by rw [length_C]; omega⟩ = (Fin.castAdd 9) (Square.idx (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 i) := by
  fin_cases i <;> rfl
private lemma context_get2 (x : Fin 36) (i : Fin 3) :
    (C x).get ⟨3+i, by rw [length_C]; omega⟩ = (Fin.natAdd 9) (Square.idx (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 i) := by
  fin_cases i <;> rfl

lemma pm_get_idx (s : Fin 6) (i : Fin 3) : (Square.C s).get i = Square.idx s i := by
  fin_cases i <;> rfl

private lemma O_commute (x : Fin 36) (i j : Fin (C x).length) :
    Commute (O ((C x).get i)) (O ((C x).get j)) := by
  change Fin 6 at i j
  refine Fin.addCases (m:=3) (n:=3) ?_ ?_ i <;> intro u
  all_goals refine Fin.addCases (m:=3) (n:=3) ?_ ?_ j <;> intro v
  · change Commute (O ((C x).get ⟨u, _⟩)) (O ((C x).get ⟨v, _⟩))
    rw [context_get1,context_get1,O_copy1,O_copy1,commute_iff_eq,tensor_mul,tensor_mul]
    congr 1
    simpa only [pm_get_idx] using (Matrices.obs_commute (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 u v).eq
  · change Commute (O ((C x).get ⟨u, _⟩)) (O ((C x).get ⟨3+v, _⟩))
    rw [context_get1,context_get2,O_copy1,O_copy2,commute_iff_eq,tensor_mul,tensor_mul]
    simp
  · change Commute (O ((C x).get ⟨3+u, _⟩)) (O ((C x).get ⟨v, _⟩))
    rw [context_get2,context_get1,O_copy2,O_copy1,commute_iff_eq,tensor_mul,tensor_mul]
    simp
  · change Commute (O ((C x).get ⟨3+u, _⟩)) (O ((C x).get ⟨3+v, _⟩))
    rw [context_get2,context_get2,O_copy2,O_copy2,commute_iff_eq,tensor_mul,tensor_mul]
    congr 1
    simpa only [pm_get_idx] using (Matrices.obs_commute (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 u v).eq

private noncomputable def effect (s : Fin 6) (a : Fin 3 → Bool) : (Matrix (Fin 4) (Fin 4) ℂ) :=
  (List.ofFn fun i => (1/2 : ℂ) • (1+(if a i then -1 else 1 : ℂ) • Matrices.obs (Square.idx s i))).prod
private noncomputable def productEffect (x : Fin 36) (a : (Fin (C x).length → Bool)) : (Matrix (Fin 16) (Fin 16) ℂ) :=
  (List.ofFn fun i => (1/2 : ℂ) • (1+(if a i then -1 else 1 : ℂ) • O ((C x).get i))).prod

private lemma effect_factor (x : Fin 36) (a : (Fin (C x).length → Bool)) :
    productEffect x a = tensor (effect (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).1)))
      (effect (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).2))) := by
  change Fin 6 → Bool at a
  have hfun : (fun i : Fin 6 =>
      (1/2 : ℂ) • (1+(if a i then -1 else 1 : ℂ) • O ((C x).get i))) =
      Fin.append
        (fun j : Fin 3 => tensor ((1/2 : ℂ) • (1+(if (((Fin.appendEquiv (α := Bool) 3 3).symm a).1) j then -1 else 1 : ℂ) • Matrices.obs (Square.idx (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 j))) 1)
        (fun j : Fin 3 => tensor 1 ((1/2 : ℂ) • (1+(if (((Fin.appendEquiv (α := Bool) 3 3).symm a).2) j then -1 else 1 : ℂ) • Matrices.obs (Square.idx (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 j)))) := by
    funext i
    refine Fin.addCases (m:=3) (n:=3) ?_ ?_ i
    · intro j
      rw [Fin.append_left]
      change (1/2 : ℂ) • (1+(if (((Fin.appendEquiv (α := Bool) 3 3).symm a).1) j then -1 else 1 : ℂ) • O ((C x).get ⟨j,_⟩)) = _
      rw [context_get1,O_copy1,tensor_proj_left]
    · intro j
      rw [Fin.append_right]
      change (1/2 : ℂ) • (1+(if (((Fin.appendEquiv (α := Bool) 3 3).symm a).2) j then -1 else 1 : ℂ) • O ((C x).get ⟨3+j,_⟩)) = _
      rw [context_get2,O_copy2,tensor_proj_right]
  change (List.ofFn (fun i : Fin 6 => (1/2 : ℂ) • (1+(if a i then -1 else 1 : ℂ) • O ((C x).get i)))).prod = _
  rw [hfun,List.ofFn_fin_append,List.prod_append]
  simp only [effect,List.ofFn,Fin.foldr_succ,Fin.foldr_zero,List.prod_cons,List.prod_nil]
  simp only [mul_one]
  simp only [tensor_mul,one_mul,mul_one]

private lemma quantum : IsQuantum C Q := by
  refine ⟨16,rho,O,rho_pos,rho_trace,O_hermitian_square,O_commute,?_⟩
  intro x a
  change (Q x a : ℂ) = (rho * productEffect x a).trace
  rw [effect_factor,← rho_tensor, tensor_mul,tensor_trace]
  have h1 := Matrices.born_probability (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).1))
  have h2 := Matrices.born_probability (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).2))
  dsimp only [Q]
  rw [Complex.ofReal_mul]
  change ((Square.P (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).1 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).1)) : ℂ) * (Square.P (((finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin (6*6)).symm) x).2 ((((Fin.appendEquiv (α := Bool) 3 3).symm a).2)) : ℂ)) = _
  rw [h1,h2]
  rfl

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product
namespace D5.S3.QuantumContext.RankOfContextualityNonPowerTwo

theorem result : claim := by
  refine ⟨18,36,Product.C,Product.Q,3,Product.quantum,Product.rank_three,?_⟩
  intro n h
  cases n with
  | zero => norm_num at h
  | succ n =>
      have he : Even (2 ^ (Nat.succ n)) := by
        refine ⟨2 ^ n, ?_⟩
        simp [pow_succ, Nat.mul_comm, two_mul]
      rcases he with ⟨k, hk⟩
      omega

end D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
