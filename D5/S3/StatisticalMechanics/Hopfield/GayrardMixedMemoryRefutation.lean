/- GID: D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.claim; result=D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result; claim=D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.claim
   digest: An asymmetric five-pattern mixed memory refutes the proposed complete hierarchy. -/

/-
proof_shape: allowable, gamma, hierarchySystem, blockVector, coefficientSet,
  memorySpin, mixedMemory, claim: definitions
proof_shape: result: bind-only (finite normalization, product-law identities, and the strong law)
escape_witness: none
admission_basis: open-problem-resolution (#13571; Refuted)
Direct frozen dependencies: D5/S3/Combinatorics/IsingUniquenessSets.sgn;
  statement_id: sha256:1589788918111821cb994915047b9b43151423396895fcfd849105cc8fe4d481
Direct frozen dependencies: D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound.c;
  statement_id: sha256:7f19041ac051a19e442a44b180bb9fd67d4dbf9b8de8e2103b65f1b9f2b48d9f
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Combinatorics.IsingUniquenessSets
import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)
open D5.S3.Quantum.Entanglement

noncomputable section
namespace D5.S3.StatisticalMechanics.Hopfield.GayrardMixedMemoryRefutation

def allowable {n : ℕ} (c : Composition n) : Prop :=
  c.blocks ≠ [] ∧ (∀ a ∈ c.blocks.dropLast, 2 ≤ a ∧ Even a) ∧
    Odd (c.blocks.getLastD 0)

def gamma {n : ℕ} (c : Composition n) (k : Fin c.length) : ℝ :=
  ((c.blocks.take (k.val + 1)).map PrecessionSpinOneSeparableBound.c).prod

def hierarchySystem {n : ℕ} (F : ℝ → ℝ) (c : Composition n) : Prop :=
  ∀ k : Fin c.length, k.val + 1 < c.length →
    2 * deriv F (gamma c k) >
      ∑ r : Fin c.length, if k < r then (c.blocksFun r : ℝ) * deriv F (gamma c r) else 0

def blockVector {n : ℕ} (c : Composition n) (μ : ℕ) : ℝ :=
  if h : μ < n then gamma c (c.index ⟨μ,h⟩) else 0

def coefficientSet (n : ℕ) (F : ℝ → ℝ) (M : ℕ) : Set (Fin M → ℝ) := by
  classical
  exact {m | ∃ c : Composition n, allowable c ∧ hierarchySystem F c ∧
    ∃ π : Equiv.Perm (Fin M), ∃ ε : Fin M → ℝ,
      (∀ μ, ε μ = -1 ∨ ε μ = 1) ∧
      ∀ μ, m μ = (ε μ) ^ (if ∀ x, deriv F (-x) = -deriv F x then 1 else 2) *
        blockVector c (π μ).val}

def memorySpin {Ω : Type*} (F : ℝ → ℝ) (M : ℕ → ℕ) (m : ℕ → ℝ)
    (ξ : ℕ → ℕ → Ω → ℝ) (N i : ℕ) (ω : Ω) : ℝ :=
  Real.sign (∑ μ ∈ Finset.range (M N), ξ μ i ω * deriv F (m μ) *
    (if m μ ≠ 0 then 1 else 0))

def mixedMemory {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (F : ℝ → ℝ) (M : ℕ → ℕ) (m : ℕ → ℝ) (ξ : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ N i, i < N → ∀ᵐ ω ∂P,
    memorySpin F M m ξ N i ω = -1 ∨ memorySpin F M m ξ N i ω = 1) ∧
  ∃ V : Finset ℕ, V.card = n ∧
    (∀ N, V ⊆ Finset.range (M N) ∧
      ∀ μ ∈ Finset.range (M N), m μ ≠ 0 ↔ μ ∈ V) ∧
    (∀ μ ∈ V, ∀ᵐ ω ∂P,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
        ξ μ i ω * memorySpin F M m ξ N i ω) atTop (𝓝 (m μ))) ∧
    (∀ μ, (∃ N, μ < M N) → μ ∉ V → ∀ᵐ ω ∂P,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
        ξ μ i ω * memorySpin F M m ξ N i ω) atTop (𝓝 0))

def claim : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → ℕ → Ω → ℝ),
    (∀ μ i, Measurable (ξ μ i)) →
    iIndepFun (fun p : ℕ × ℕ => ξ p.1 p.2) P →
    (∀ μ i, P {ω | ξ μ i ω = 1} = 1/2 ∧ P {ω | ξ μ i ω = -1} = 1/2) →
    ∀ (F : ℝ → ℝ), ContDiff ℝ ⊤ F → (∀ x, 0 < x → 0 < deriv F x) →
    ∀ (n : ℕ), Odd n → ∀ (M : ℕ → ℕ), Monotone M →
    ∀ (m : ℕ → ℝ), (∀ μ, -1 ≤ m μ ∧ m μ ≤ 1) →
      (mixedMemory P n F M m ξ ↔
        ∀ N, (fun μ : Fin (M N) => m μ.val) ∈ coefficientSet n F (M N))

/-- Gayrard's Conjecture 1.4 fails at the positive-margin vector
`(5/8,3/8,3/8,1/8,1/8)` for the classical quadratic activation. -/
theorem result : ¬ claim := by
  classical
  intro hall
  let w : Fin 5 → ℤ := ![5,3,3,1,1]
  let m : ℕ → ℝ := fun μ => if h : μ < 5 then (w ⟨μ,h⟩ : ℝ)/8 else 0
  let F : ℝ → ℝ := fun x => x^2/2
  have hderiv (x : ℝ) : deriv F x = x := by
    dsimp [F]
    rw [deriv_div_const, deriv_pow_field]
    norm_num
  have hF : ContDiff ℝ ⊤ F := by dsimp [F]; fun_prop
  have hm (μ : ℕ) : -1 ≤ m μ ∧ m μ ≤ 1 := by
    dsimp [m]
    split_ifs with h
    · interval_cases μ <;> norm_num [w]
    · norm_num
  have hwn : ∀ k : Fin 5, w k ≠ 0 := by decide +kernel
  have htable : ∀ j : Fin 5,
      (∑ x : Fin 5 → Bool, (if x j then (1 : ℤ) else -1) *
        Int.sign (∑ k : Fin 5, w k * (if x k then (1 : ℤ) else -1))) = 4 * w j := by
    decide +kernel
  have hzero : ∀ x : Fin 5 → Bool,
      (∑ k : Fin 5, w k * (if x k then (1 : ℤ) else -1)) ≠ 0 := by decide +kernel
  have hcast (b : Bool) : sgn b = ((if b then (1 : ℤ) else -1) : ℝ) := by
    cases b <;> simp [sgn]
  have hscale (z : ℤ) : Real.sign ((z : ℝ) / 8) = (Int.sign z : ℝ) := by
    rw [← Real.sign_intCast]
    rcases lt_trichotomy (z : ℝ) 0 with hz | hz | hz
    · rw [Real.sign_of_neg (div_neg_of_neg_of_pos hz (by norm_num)), Real.sign_of_neg hz]
    · simp [hz]
    · rw [Real.sign_of_pos (div_pos hz (by norm_num)), Real.sign_of_pos hz]
  have hfield (x : Fin 5 → Bool) :
      (∑ k : Fin 5, ((w k : ℝ)/8) * sgn (x k)) =
        ((∑ k : Fin 5, w k * (if x k then (1 : ℤ) else -1) : ℤ) : ℝ)/8 := by
    push_cast
    simp only [hcast, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    cases x k <;> norm_num <;> ring
  have hmean (j : Fin 5) :
      (1/32:ℝ) * ∑ x : Fin 5 → Bool, sgn (x j) *
        Real.sign (∑ k : Fin 5, ((w k : ℝ)/8) * sgn (x k)) = (w j : ℝ)/8 := by
    have ht : (∑ x : Fin 5 → Bool, sgn (x j) * (Int.sign (∑ k : Fin 5, w k * (if x k then (1 : ℤ) else -1)) : ℝ)) = 4 * (w j : ℝ) := by
      simp only [hcast]
      exact_mod_cast htable j
    simp_rw [hfield,hscale]
    rw [ht]
    ring
  have hgamma (c : Composition 5) (hc : allowable c) : ∀ k : Fin c.length, |gamma c k| ≤ 1/2 := by
    have comp5 (c : Composition 5) (hc : allowable c) :
        c.blocks = [5] ∨ c.blocks = [2,3] ∨ c.blocks = [4,1] ∨ c.blocks = [2,2,1] := by
      have hsum := c.blocks_sum
      have hpos : ∀ a ∈ c.blocks, 0 < a := fun a ha => c.blocks_pos ha
      rcases hc with ⟨hne,he,ho⟩
      rcases h : c.blocks with _ | ⟨a,tail⟩
      · exact (hne h).elim
      rcases tail with _ | ⟨b,tail⟩
      · simp only [h, List.sum_cons, List.sum_nil, add_zero] at hsum
        exact Or.inl (by simp [hsum])
      rcases tail with _ | ⟨d,tail⟩
      · have ha := he a (by simp [h])
        have hb := hpos b (by simp [h] : b ∈ c.blocks)
        simp only [h, List.sum_cons, List.sum_nil, add_zero] at hsum
        have ha2 : a % 2 = 0 := Nat.even_iff.mp ha.2
        have ha' : a = 2 ∨ a = 4 := by omega
        rcases ha' with rfl | rfl
        · have hb3 : b = 3 := by omega
          right; left; simp [hb3]
        · have hb1 : b = 1 := by omega
          right; right; left; simp [hb1]
      rcases tail with _ | ⟨e,tail⟩
      · have ha := he a (by simp [h])
        have hb := he b (by simp [h])
        have hd := hpos d (by simp [h] : d ∈ c.blocks)
        simp only [h, List.sum_cons, List.sum_nil, add_zero] at hsum
        have : a = 2 ∧ b = 2 ∧ d = 1 := by omega
        right; right; right; simp [this.1,this.2.1,this.2.2]
      · have ha := he a (by simp [h])
        have hb := he b (by simp [h])
        have hd := he d (by simp [h])
        have he' := hpos e (by simp [h] : e ∈ c.blocks)
        simp only [h, List.sum_cons] at hsum
        omega
    intro k
    rcases comp5 c hc with h | h | h | h
    all_goals
      have hk := k.isLt
      simp only [Composition.length, h, List.length_cons, List.length_nil] at hk
    · have hk0 : k.val = 0 := by omega
      norm_num [gamma, h, hk0, PrecessionSpinOneSeparableBound.c, Nat.choose]
    · interval_cases hkval : k.val <;> norm_num [gamma,h,hkval,PrecessionSpinOneSeparableBound.c,Nat.choose]
    · interval_cases hkval : k.val <;> norm_num [gamma,h,hkval,PrecessionSpinOneSeparableBound.c,Nat.choose]
    · interval_cases hkval : k.val <;> norm_num [gamma,h,hkval,PrecessionSpinOneSeparableBound.c,Nat.choose]
  have hblock (c : Composition 5) (hc : allowable c) (μ : ℕ) : |blockVector c μ| ≤ 1/2 := by
    unfold blockVector
    split_ifs with h
    · exact hgamma c hc _
    · norm_num
  have hnot : (fun μ : Fin 5 => m μ.val) ∉ coefficientSet 5 F 5 := by
    rintro ⟨c,hc,_,π,ε,hε,heq⟩
    have hh := hblock c hc (π 0).val
    have he : |ε 0| = 1 := by rcases hε 0 with he | he <;> simp [he]
    have hp : |(ε 0) ^ (if ∀ x, deriv F (-x) = -deriv F x then 1 else 2)| = 1 := by
      rw [abs_pow,he,one_pow]
    have hh' : |m 0| ≤ 1/2 := by
      have heq0 := heq 0
      change m 0 = _ at heq0
      rw [heq0,abs_mul,hp,one_mul]
      exact hh
    norm_num [m,w] at hh'
  let b := (PMF.uniformOfFintype Bool).toMeasure
  let q := Measure.infinitePi (fun _ : ℕ => b)
  let P := Measure.infinitePi (fun _ : ℕ => q)
  let ξ : ℕ → ℕ → (ℕ → ℕ → Bool) → ℝ := fun μ i ω => sgn (ω i μ)
  have hξ (μ i : ℕ) : Measurable (ξ μ i) :=
    (show Measurable sgn from Measurable.of_discrete).comp
      ((measurable_pi_apply μ).comp (measurable_pi_apply i))
  have hi : iIndepFun (fun p : ℕ × ℕ => ξ p.1 p.2) P := by
    have hh : iIndepFun (fun p : ℕ × ℕ => fun ω : ℕ → ℕ → Bool => sgn (ω p.1 p.2)) P :=
      iIndepFun_uncurry_infinitePi' (X := fun _ _ => sgn)
        (fun _ _ : ℕ => b) (fun _ _ => Measurable.of_discrete)
    exact hh.precomp (g := fun p : ℕ × ℕ => (p.2,p.1))
      (by intro a b h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  have hrow (i : ℕ) : HasLaw (fun ω : ℕ → ℕ → Bool => ω i) q P :=
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval (fun _ => q) i⟩
  have hbool (μ i : ℕ) : HasLaw (fun ω : ℕ → ℕ → Bool => ω i μ) b P :=
    (show HasLaw (fun row : ℕ → Bool => row μ) b q from
      ⟨(measurable_pi_apply μ).aemeasurable, Measure.infinitePi_map_eval (fun _ => b) μ⟩).comp (hrow i)
  have hmass (μ i : ℕ) : P {ω | ξ μ i ω = 1} = 1/2 ∧ P {ω | ξ μ i ω = -1} = 1/2 := by
    have hp := (hbool μ i).measure_eq (p := fun x => sgn x = 1) (MeasurableSet.of_discrete)
    have hn := (hbool μ i).measure_eq (p := fun x => sgn x = -1) (MeasurableSet.of_discrete)
    have heqp : {x : Bool | sgn x = 1} = {true} := by ext x; cases x <;> norm_num [sgn]
    have heqn : {x : Bool | sgn x = -1} = {false} := by ext x; cases x <;> norm_num [sgn]
    rw [heqp] at hp
    rw [heqn] at hn
    simpa [b,ξ,PMF.uniformOfFintype_apply] using And.intro hp hn
  have hspin (N i : ℕ) (ω : ℕ → ℕ → Bool) :
      memorySpin F (fun _ => 5) m ξ N i ω =
        Real.sign (∑ k : Fin 5, ((w k : ℝ)/8) * sgn (ω i k.val)) := by
    unfold memorySpin
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hn : (w k : ℝ)/8 ≠ 0 := div_ne_zero (Int.cast_ne_zero.mpr (hwn k)) (by norm_num)
    simp [ξ,m,k.isLt,hderiv,hn]
    ring
  have hfinite (f : (Fin 5 → Bool) → ℝ) :
      (∫ x, f (fun j : Fin 5 => x j.val) ∂q) = (1/32:ℝ) * ∑ x : Fin 5 → Bool, f x := by
    have hb (a : Bool) : b {a} = 1/2 := by
      simp [b, PMF.uniformOfFintype_apply]
    have hi : iIndepFun (fun j : Fin 5 => fun x : ℕ → Bool => x j.val) q :=
      (iIndepFun_infinitePi (X := fun _ : ℕ => (id : Bool → Bool))
        (P := fun _ => b) (fun _ => measurable_id)).precomp Fin.val_injective
    have hlaw : q.map (fun x (j : Fin 5) => x j.val) = Measure.pi (fun _ : Fin 5 => b) := by
      rw [hi.map_fun_eq_pi_map (fun j => (measurable_pi_apply j.val).aemeasurable)]
      simp [q, Measure.infinitePi_map_eval]
    have hm : Measurable f := Measurable.of_discrete
    change (∫ x, f (fun j : Fin 5 => x j.val) ∂q) = _
    rw [← integral_map (μ := q) (φ := fun x (j : Fin 5) => x j.val)
      (Measurable.of_eval (fun j => measurable_pi_apply j.val)).aemeasurable
      hm.aestronglyMeasurable, hlaw, integral_fintype Integrable.of_finite]
    simp only [measureReal_def, Measure.pi_singleton, hb, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num [smul_eq_mul, ← Finset.mul_sum]
  have hslln (j : Fin 5) : ∀ᵐ ω ∂P,
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
        ξ j.val i ω * memorySpin F (fun _ => 5) m ξ N i ω) atTop (𝓝 (m j.val)) := by
    let f : (Fin 5 → Bool) → ℝ := fun x => sgn (x j) *
      Real.sign (∑ k : Fin 5, ((w k : ℝ)/8) * sgn (x k))
    let g : (ℕ → Bool) → ℝ := fun x => f (fun k : Fin 5 => x k.val)
    let X : ℕ → (ℕ → ℕ → Bool) → ℝ := fun i ω => g (ω i)
    have hfm : Measurable f := Measurable.of_discrete
    have hgm : Measurable g := hfm.comp (show Measurable (fun x : ℕ → Bool => fun k : Fin 5 => x k.val) from
      Measurable.of_eval (fun k => measurable_pi_apply k.val))
    have hrows : iIndepFun (fun i : ℕ => fun ω : ℕ → ℕ → Bool => ω i) P :=
      iIndepFun_infinitePi (P := fun _ => q) (X := fun _ => id) (fun _ => measurable_id)
    have hX : iIndepFun X P := hrows.comp (fun _ => g) (fun _ => hgm)
    have hid (i : ℕ) : IdentDistrib (X i) (X 0) P P :=
      ((hrow i).identDistrib (hrow 0)).comp hgm
    have hib : iIndepFun (fun k : Fin 5 => fun x : ℕ → Bool => x k.val) q :=
      (iIndepFun_infinitePi (X := fun _ : ℕ => (id : Bool → Bool))
        (P := fun _ => b) (fun _ => measurable_id)).precomp Fin.val_injective
    have hproj : HasLaw (fun x : ℕ → Bool => fun k : Fin 5 => x k.val)
        (Measure.pi (fun _ : Fin 5 => b)) q := by
      refine ⟨(Measurable.of_eval (fun k => measurable_pi_apply k.val)).aemeasurable, ?_⟩
      rw [hib.map_fun_eq_pi_map (fun k => (measurable_pi_apply k.val).aemeasurable)]
      simp [q, Measure.infinitePi_map_eval]
    have htotal := hproj.comp (hrow 0)
    have hint : Integrable (X 0) P := by
      apply (integrable_map_measure hfm.aestronglyMeasurable htotal.aemeasurable).mp
      rw [htotal.map_eq]
      exact Integrable.of_finite
    have hexp : (∫ ω, X 0 ω ∂P) = m j.val := by
      calc
        _ = ∫ x, g x ∂q := (hrow 0).integral_comp hgm.aestronglyMeasurable
        _ = (1/32:ℝ) * ∑ x : Fin 5 → Bool, f x := hfinite f
        _ = (w j : ℝ)/8 := hmean j
        _ = m j.val := by simp [m,j.isLt]
    have hs := strong_law_ae X hint (fun i k hik => hX.indepFun hik) hid
    simpa only [smul_eq_mul,hexp,X,g,f,ξ,hspin] using hs
  have hmem : mixedMemory P 5 F (fun _ => 5) m ξ := by
    constructor
    · intro N i hi
      apply Filter.Eventually.of_forall
      intro ω
      rw [hspin]
      apply Real.sign_apply_eq_of_ne_zero
      rw [hfield]
      exact div_ne_zero (Int.cast_ne_zero.mpr (hzero _)) (by norm_num)
    · refine ⟨Finset.range 5,by simp,?_,?_,?_⟩
      · intro N
        refine ⟨Finset.Subset.refl _,?_⟩
        intro μ hμ
        have hμ' := Finset.mem_range.mp hμ
        have hn : m μ ≠ 0 := by
          simp only [m,dif_pos hμ']
          exact div_ne_zero (Int.cast_ne_zero.mpr (hwn _)) (by norm_num)
        simp [hn,hμ]
      · intro μ hμ
        exact hslln ⟨μ,Finset.mem_range.mp hμ⟩
      · intro μ hμ hn
        obtain ⟨N,hN⟩ := hμ
        exact (hn (Finset.mem_range.mpr hN)).elim
  have hiff := hall (ℕ → ℕ → Bool) P ξ hξ hi hmass F hF
    (fun x hx => by simpa only [hderiv] using hx) 5 (by decide) (fun _ => 5)
    (fun _ _ _ => le_refl _) m hm
  exact hnot (hiff.mp hmem 0)

#print axioms result
end D5.S3.StatisticalMechanics.Hopfield.GayrardMixedMemoryRefutation
