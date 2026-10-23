/- GID: D5/S3/Quantum/Entanglement/EJMWightedCancellation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJMWightedCancellation
   mirror-E: none(waiver:exact-inflation-certificate-consumer)
   anchors: []
   utility: none
   digest: Finite weighted contractions preserve actual triangle party order. -/

/-
The finite cancellation and order adapters are bind-only helpers for the exact
inflation consumer; they do not establish positivity of the EJM score.
The target numerator is the ideal EJM law in Gitton and Renner's pinned
ejm_224_nl_certificate experiment, not a symmetry assumption on the lift.
-/

import D5.S3.Quantum.Entanglement.TriangleInflationSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Entanglement.EJMWightedCancellation
open D5.S3.Quantum.Entanglement.TriangleInflationSoundness
open scoped BigOperators

def ejmNumerator (a b c : Fin 4) : ℝ :=
  if a = b ∧ b = c then 25
  else if a ≠ b ∧ b ≠ c ∧ c ≠ a then 5
  else 1

theorem ejmNumerator_swap_ab (a b c : Fin 4) :
    ejmNumerator b a c = ejmNumerator a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [ejmNumerator]

theorem ejmNumerator_sum (a : Fin 4) :
    (∑ b : Fin 4, ∑ c : Fin 4, ejmNumerator a b c) = 64 := by
  fin_cases a <;>
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ejmNumerator]

variable {A B : Type*} [Fintype A] [Fintype B]

theorem finite_weighted_block_cancellation
    (m : A → B → ℝ) (p : A → ℝ) (k : B → ℝ)
    (F : A → B → ℝ)
    (hfactor : ∀ a b, m a b = p a * k b) :
    (∑ a, ∑ b, m a b * F a b) =
      ∑ b, (∑ a, p a * F a b) * k b := by
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem finite_scaled_weighted_block_cancellation
    (lhsScale rhsScale : ℝ) (targetDenom : ℝ)
    (m : A → B → ℝ) (targetNum : A → ℝ) (k : B → ℝ)
    (F : A → B → ℝ)
    (hfactor : ∀ a b, m a b = (targetNum a / targetDenom) * k b)
    (hscale : lhsScale / targetDenom = -rhsScale) :
    lhsScale * (∑ a, ∑ b, m a b * F a b) +
        rhsScale * (∑ b, (∑ a, targetNum a * F a b) * k b) = 0 := by
  rw [finite_weighted_block_cancellation m (fun a => targetNum a / targetDenom) k F hfactor]
  have hweighted :
      lhsScale * (∑ b, (∑ a, targetNum a / targetDenom * F a b) * k b) =
        -rhsScale * (∑ b, (∑ a, targetNum a * F a b) * k b) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (lhsScale / targetDenom) * (targetNum a * F a b * k b) := by ring
      _ = _ := by rw [hscale]
  rw [hweighted]
  ring

theorem triangle_mass_in_BAC_order
    {Copy Node : Type*} [Fintype Copy] [Fintype Node]
    [DecidableEq Copy] [DecidableEq Node]
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (vA vB vC : Node) (α β γ : Copy) (o : Node → Outcome)
    (hA : S.party vA = 0) (hB : S.party vB = 1) (hC : S.party vC = 2)
    (hA₁ : S.firstCopy vA = β) (hA₂ : S.secondCopy vA = γ)
    (hB₁ : S.firstCopy vB = γ) (hB₂ : S.secondCopy vB = α)
    (hC₁ : S.firstCopy vC = α) (hC₂ : S.secondCopy vC = β) :
    marginalMass S R ({vB, vA, vC} : Finset Node) o =
      p (o vA) (o vB) (o vC) := by
  have h := marginalMass_triangle S R p hp vA vB vC α β γ o
    hA hB hC hA₁ hA₂ hB₁ hB₂ hC₁ hC₂
  simpa [Finset.insert_comm] using h

theorem singleton_mass_in_B_order
    {Copy Node : Type*} [Fintype Copy] [Fintype Node]
    [DecidableEq Copy] [DecidableEq Node]
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (p : Outcome → Outcome → Outcome → ℝ) (hp : Represents R p)
    (vA vB vC : Node) (α β γ : Copy) (o : Node → Outcome)
    (hA : S.party vA = 0) (hB : S.party vB = 1) (hC : S.party vC = 2)
    (hA₁ : S.firstCopy vA = β) (hA₂ : S.secondCopy vA = γ)
    (hB₁ : S.firstCopy vB = γ) (hB₂ : S.secondCopy vB = α)
    (hC₁ : S.firstCopy vC = α) (hC₂ : S.secondCopy vC = β) :
    marginalMass S R ({vB} : Finset Node) o =
      ∑ a : Outcome, ∑ c : Outcome, p a (o vB) c := by
  exact marginalMass_singleton_B S R p hp vA vB vC α β γ o
    hA hB hC hA₁ hA₂ hB₁ hB₂ hC₁ hC₂

section Projection

variable {Copy Node Ix : Type*} [Fintype Copy] [Fintype Node] [Fintype Ix]
  [DecidableEq Copy] [DecidableEq Node] [DecidableEq Ix]

def nodeRange (q : Ix → Node) : Finset Node := Finset.univ.image q

private noncomputable def nodeRangeEquiv (q : Ix → Node) (hq : Function.Injective q) :
    Ix ≃ {v : Node // v ∈ nodeRange q} :=
  Equiv.ofBijective (fun i => ⟨q i, by simp [nodeRange]⟩) ⟨
    by intro i j h; exact hq (congrArg Subtype.val h),
    by intro v; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.property
       exact ⟨i, Subtype.ext hi⟩⟩

/-- Actual observable coordinates split into a retained tuple and its complement. -/
noncomputable def tupleSplit (q : Ix → Node) (hq : Function.Injective q) :
    (Node → Outcome) ≃ (Ix → Outcome) × ({v : Node // v ∉ nodeRange q} → Outcome) :=
  (Equiv.piEquivPiSubtypeProd (fun v => v ∈ nodeRange q) (fun _ => Outcome)).trans
    (Equiv.prodCongr (Equiv.piCongrLeft (fun _ => Outcome) (nodeRangeEquiv q hq)).symm
      (Equiv.refl _))

private theorem tupleSplit_fst (q : Ix → Node) (hq : Function.Injective q)
    (o : Node → Outcome) : (tupleSplit q hq o).1 = o ∘ q := by
  rfl

private theorem tupleSplit_symm_fst (q : Ix → Node) (hq : Function.Injective q)
    (a : Ix → Outcome) (z : {v : Node // v ∉ nodeRange q} → Outcome) :
    (tupleSplit q hq).symm (a,z) ∘ q = a := by
  simpa only [tupleSplit_fst] using congrArg Prod.fst ((tupleSplit q hq).apply_symm_apply (a,z))

/-- The tuple marginal is derived from the full continuous-source lift. -/
def tupleMass (S : InflationSpec Copy Node) (R : ResponseModel)
    (q : Ix → Node) (hq : Function.Injective q) (a : Ix → Outcome) : ℝ :=
  marginalMass S R (nodeRange q) ((tupleSplit q hq).symm (a, fun _ => 0))

private theorem tupleMass_fiber_sum (S : InflationSpec Copy Node) (R : ResponseModel)
    (q : Ix → Node) (hq : Function.Injective q) (a : Ix → Outcome) :
    (∑ z, inflationMass S R ((tupleSplit q hq).symm (a,z))) =
      tupleMass S R q hq a := by
  let o := (tupleSplit q hq).symm (a, fun _ => 0)
  have hrestrict : (fun v : {v : Node // v ∈ nodeRange q} => o v) =
      Equiv.piCongrLeft (fun _ => Outcome) (nodeRangeEquiv q hq) a := by
    have h := congrArg Prod.fst
      ((Equiv.piEquivPiSubtypeProd (fun v => v ∈ nodeRange q) (fun _ => Outcome)).apply_symm_apply
        (Equiv.piCongrLeft (fun _ => Outcome) (nodeRangeEquiv q hq) a, fun _ => 0))
    exact h
  have h := inflationMass_marginal S R (nodeRange q) o
  rw [hrestrict] at h
  exact h

/-- An arbitrary observable tuple score has its expectation under the actual
lift equal to its expectation under the derived tuple marginal. -/
theorem inflation_expectation_tuple (S : InflationSpec Copy Node) (R : ResponseModel)
    (q : Ix → Node) (hq : Function.Injective q) (F : (Ix → Outcome) → ℝ) :
    (∑ o : Node → Outcome, inflationMass S R o * F (o ∘ q)) =
      ∑ a : Ix → Outcome, tupleMass S R q hq a * F a := by
  classical
  rw [← (tupleSplit q hq).symm.sum_comp
    (fun o : Node → Outcome => inflationMass S R o * F (o ∘ q)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [tupleSplit_symm_fst]
  rw [← Finset.sum_mul, tupleMass_fiber_sum]

private theorem marginalMass_congr (S : InflationSpec Copy Node) (R : ResponseModel)
    (J : Finset Node) (o o' : Node → Outcome) (h : ∀ v ∈ J, o v = o' v) :
    marginalMass S R J o = marginalMass S R J o' := by
  unfold marginalMass
  congr 1
  funext u
  exact Finset.prod_congr rfl (fun v hv => by rw [h v hv])

private theorem tupleMass_congr (S : InflationSpec Copy Node) (R : ResponseModel)
    (q : Ix → Node) (hq : Function.Injective q) (o : Node → Outcome) :
    tupleMass S R q hq (o ∘ q) = marginalMass S R (nodeRange q) o := by
  apply marginalMass_congr
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact congrFun (tupleSplit_symm_fst q hq (o ∘ q) (fun _ => 0)) i

end Projection

section Centered

variable {Copy Node Head Tail : Type*}
  [Fintype Copy] [Fintype Node] [Fintype Head] [Fintype Tail]
  [DecidableEq Copy] [DecidableEq Node] [DecidableEq Head] [DecidableEq Tail]

/-- The finite score of a truly factorized lifted block has zero expectation.
No symmetry of the response model or its observable lift is assumed. -/
theorem inflation_centered_expectation
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (q : Head ⊕ Tail → Node) (hq : Function.Injective q)
    (targetNum : (Head → Outcome) → ℝ) (targetDenom lhsScale rhsScale : ℝ)
    (F : ((Head ⊕ Tail) → Outcome) → ℝ)
    (hscale : lhsScale / targetDenom = -rhsScale)
    (hsource : Disjoint (sourceSupport S (nodeRange (q ∘ Sum.inl)))
      (sourceSupport S (nodeRange (q ∘ Sum.inr))))
    (hhead : ∀ o : Node → Outcome,
      marginalMass S R (nodeRange (q ∘ Sum.inl)) o =
        targetNum (o ∘ q ∘ Sum.inl) / targetDenom) :
    (∑ o : Node → Outcome, inflationMass S R o *
      (lhsScale * F (o ∘ q) + rhsScale *
        (∑ a : Head → Outcome, targetNum a * F (Sum.elim a (o ∘ q ∘ Sum.inr))))) = 0 := by
  classical
  have hqinl : Function.Injective (q ∘ Sum.inl) := hq.comp Sum.inl_injective
  have hqinr : Function.Injective (q ∘ Sum.inr) := hq.comp Sum.inr_injective
  have hrange : nodeRange q = nodeRange (q ∘ Sum.inl) ∪ nodeRange (q ∘ Sum.inr) := by
    ext v
    simp only [nodeRange, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  have hdisjoint : Disjoint (nodeRange (q ∘ Sum.inl)) (nodeRange (q ∘ Sum.inr)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hv'
    have h := hq (ha.trans hb.symm)
    cases h
  have hfactor (a : Head → Outcome) (b : Tail → Outcome) :
      tupleMass S R q hq (Sum.elim a b) =
        (targetNum a / targetDenom) * tupleMass S R (q ∘ Sum.inr) hqinr b := by
    let o := (tupleSplit q hq).symm (Sum.elim a b, fun _ => 0)
    have hproj : o ∘ q = Sum.elim a b := tupleSplit_symm_fst q hq _ _
    have hinl : o ∘ q ∘ Sum.inl = a := by funext i; exact congrFun hproj (Sum.inl i)
    have hinr : o ∘ q ∘ Sum.inr = b := by funext i; exact congrFun hproj (Sum.inr i)
    change marginalMass S R (nodeRange q) o = _
    rw [hrange, marginalMass_disjoint_source_factorization S R _ _ o hdisjoint hsource,
      hhead, hinl, ← tupleMass_congr S R (q ∘ Sum.inr) hqinr o, hinr]
  have hjoint : (∑ o : Node → Outcome, inflationMass S R o * F (o ∘ q)) =
      ∑ a : Head → Outcome, ∑ b : Tail → Outcome,
        tupleMass S R q hq (Sum.elim a b) * F (Sum.elim a b) := by
    rw [inflation_expectation_tuple S R q hq F,
      ← (Equiv.sumArrowEquivProdArrow Head Tail Outcome).symm.sum_comp
        (fun a => tupleMass S R q hq a * F a), Fintype.sum_prod_type]
    rfl
  have htail := inflation_expectation_tuple S R (q ∘ Sum.inr) hqinr
    (fun b => ∑ a : Head → Outcome, targetNum a * F (Sum.elim a b))
  have hlinear : (∑ o : Node → Outcome, inflationMass S R o *
      (lhsScale * F (o ∘ q) + rhsScale *
        (∑ a : Head → Outcome, targetNum a * F (Sum.elim a (o ∘ q ∘ Sum.inr))))) =
      lhsScale * (∑ o : Node → Outcome, inflationMass S R o * F (o ∘ q)) +
        rhsScale * (∑ o : Node → Outcome, inflationMass S R o *
          (∑ a : Head → Outcome, targetNum a * F (Sum.elim a (o ∘ q ∘ Sum.inr)))) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;>
      intro o _ <;> ring
  rw [hlinear, hjoint, htail]
  simpa only [mul_comm] using finite_scaled_weighted_block_cancellation
    lhsScale rhsScale targetDenom
    (fun a b => tupleMass S R q hq (Sum.elim a b)) targetNum
    (tupleMass S R (q ∘ Sum.inr) hqinr) (fun a b => F (Sum.elim a b)) hfactor hscale

end Centered

private theorem elim_comp_finSum {m n : ℕ} (a : Fin m → Outcome) (b : Fin n → Outcome) :
    Sum.elim a b ∘ (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm = Fin.append a b := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

/-- Tuple-indexed version consumed by the original ten- and nine-node EJM
coefficient tables, in their exact head-then-tail order. -/
theorem inflation_centered_fin_expectation
    {Copy Node : Type*} [Fintype Copy] [Fintype Node]
    [DecidableEq Copy] [DecidableEq Node] {m n : ℕ}
    (S : InflationSpec Copy Node) (R : ResponseModel)
    (q : Fin (m + n) → Node) (hq : Function.Injective q)
    (targetNum : (Fin m → Outcome) → ℝ) (targetDenom lhsScale rhsScale : ℝ)
    (F : (Fin (m + n) → Outcome) → ℝ)
    (hscale : lhsScale / targetDenom = -rhsScale)
    (hsource : Disjoint (sourceSupport S (nodeRange (fun i => q (Fin.castAdd n i))))
      (sourceSupport S (nodeRange (fun i => q (Fin.natAdd m i)))))
    (hhead : ∀ o : Node → Outcome,
      marginalMass S R (nodeRange (fun i => q (Fin.castAdd n i))) o =
        targetNum (fun i => o (q (Fin.castAdd n i))) / targetDenom) :
    (∑ o : Node → Outcome, inflationMass S R o *
      (lhsScale * F (o ∘ q) + rhsScale *
        (∑ a : Fin m → Outcome, targetNum a *
          F (Fin.append a (fun i => o (q (Fin.natAdd m i))))))) = 0 := by
  classical
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  have h := inflation_centered_expectation S R (q ∘ e) (hq.comp e.injective)
    targetNum targetDenom lhsScale rhsScale (fun a => F (a ∘ e.symm)) hscale hsource hhead
  have hcomp (o : Node → Outcome) : (o ∘ (q ∘ e)) ∘ e.symm = o ∘ q := by
    funext i
    simp [e]
  have happend (a : Fin m → Outcome) (o : Node → Outcome) :
      Sum.elim a (o ∘ (q ∘ e) ∘ Sum.inr) ∘ e.symm =
        Fin.append a (fun i => o (q (Fin.natAdd m i))) := by
    change Sum.elim a (fun i => o (q (Fin.natAdd m i))) ∘ finSumFinEquiv.symm = _
    exact elim_comp_finSum _ _
  simpa only [hcomp, happend] using h

end D5.S3.Quantum.Entanglement.EJMWightedCancellation
