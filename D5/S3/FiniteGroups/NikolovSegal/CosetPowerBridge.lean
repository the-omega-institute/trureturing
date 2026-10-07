/- GID: D5/S3/FiniteGroups/NikolovSegal/CosetPowerBridge
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/CosetPowerBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered commutator-value coverage implies exact prescribed coset-power surjectivity. -/

import D5.S3.Factorization.Galois.ProfinitePowerTransfer
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Group

set_option autoImplicit false

/-!
The ordered algebra in Nikolov--Segal, *On finitely generated profinite groups,
I*, Annals of Mathematics 165 (2007), printed pp. 227--228, equation (43) and
the reduction of Proposition 10.1 to Proposition 10.2.
DOI: 10.4007/annals.2007.165.171.

The commutator-value coverage premise below is an explicit unproved input.
No finite-simple-group width theorem is asserted by this module.
-/

open D5.S3.Factorization.Galois.PowerCompactness
  D5.S3.Factorization.Galois.ProfinitePowerTransfer

open scoped commutatorElement

namespace NikolovSegal

universe u
variable {G : Type u} [Group G]

/-- Paper right conjugation, as opposed to Mathlib's left conjugation. -/
def paperConj (x g : G) : G := g⁻¹ * x * g

/-- Paper commutator, as opposed to Mathlib's `x*y*x⁻¹*y⁻¹`. -/
def paperComm (x y : G) : G := x⁻¹ * y⁻¹ * x * y

theorem paperConj_eq_mathlib (x g : G) :
    paperConj x g = MulAut.conj g⁻¹ x := by
  simp [paperConj]

theorem paperComm_eq_mathlib (x y : G) :
    paperComm x y = ⁅x⁻¹, y⁻¹⁆ := by
  simp [paperComm, commutatorElement_def]

private theorem paperConj_pow (x g : G) (q : ℕ) :
    paperConj x g ^ q = paperConj (x ^ q) g := by
  simp only [paperConj_eq_mathlib, map_pow]

/-- Ordered products and prefixes; the prefix ends strictly before position `i`. -/
def orderedProduct {m : ℕ} (f : Fin m → G) : G := (List.ofFn f).prod

def prefixProduct {m : ℕ} (f : Fin m → G) (i : ℕ) : G :=
  ((List.ofFn f).take i).prod

private theorem orderedProduct_succ {m : ℕ} (f : Fin (m + 1) → G) :
    orderedProduct f = orderedProduct (fun i => f i.castSucc) * f (Fin.last m) := by
  unfold orderedProduct
  rw [List.ofFn_succ', List.prod_concat]

private theorem prefixProduct_castSucc {m : ℕ} (f : Fin (m + 1) → G) (i : Fin m) :
    prefixProduct f i.castSucc.val = prefixProduct (fun j => f j.castSucc) i.val := by
  simp only [prefixProduct, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc]
  rw [List.take_append_of_le_length]
  simp

private theorem prefixProduct_last {m : ℕ} (f : Fin (m + 1) → G) :
    prefixProduct f (Fin.last m).val = orderedProduct (fun j => f j.castSucc) := by
  unfold prefixProduct orderedProduct
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [Fin.val_last, List.take_append, List.length_ofFn, Nat.sub_self,
    List.take_zero, List.append_nil]
  rw [List.take_of_length_le (by simp)]

private theorem powerProduct_eq_ordered (q m : ℕ) (f : Fin m → G) :
    powerProduct q m f = orderedProduct (fun i => f i ^ q) := by
  rw [powerProduct, orderedProduct, List.ofFn_eq_map]

private theorem map_orderedProduct {K : Type*} [Group K] (f : G →* K)
    {m : ℕ} (t : Fin m → G) :
    f (orderedProduct t) = orderedProduct (fun i => f (t i)) := by
  simp [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def]

/-- The inverse ordered prefix `τᵢ`, in the paper's order. -/
def powerPrefix (q : ℕ) {m : ℕ} (h : Fin m → G) (i : Fin m) : G :=
  (prefixProduct (fun j => h j ^ q) i.val)⁻¹

/-- Ordered conjugated-product collection: the algebraic core of equation (43). -/
theorem conjugated_product_collection {m : ℕ} (z b : Fin m → G) :
    orderedProduct (fun i => paperConj (z i) (b i)) =
      orderedProduct (fun i =>
        paperConj (paperComm (b i) (z i)⁻¹) (prefixProduct z i.val)⁻¹) *
      orderedProduct z := by
  induction m with
  | zero => simp [orderedProduct]
  | succ m ih =>
    rw [orderedProduct_succ, orderedProduct_succ, orderedProduct_succ,
      ih (fun i => z i.castSucc) (fun i => b i.castSucc)]
    simp only [prefixProduct_castSucc, prefixProduct_last]
    simp only [paperConj, paperComm]
    group

/-- The paper's change of variables `aᵢ = xᵢ^bᵢ [bᵢ,hᵢ⁻¹]`. -/
def cosetChange {m : ℕ} (x b h : Fin m → G) (i : Fin m) : G :=
  paperConj (x i) (b i) * paperComm (b i) (h i)⁻¹

private theorem cosetChange_mul {m : ℕ} (x b h : Fin m → G) (i : Fin m) :
    cosetChange x b h i * h i = paperConj (x i * h i) (b i) := by
  simp only [cosetChange, paperConj, paperComm]
  group

/-- Equation (43), including the rightmost `ψ(x)` and the ordered prefix corrections. -/
theorem equation43 (q m : ℕ) (x b h : Fin m → G) :
    powerProduct q m (fun i => cosetChange x b h i * h i) *
        (powerProduct q m h)⁻¹ =
      orderedProduct (fun i =>
        paperConj (paperComm (b i) ((x i * h i) ^ q)⁻¹)
          (powerPrefix q (fun j => x j * h j) i)) *
      (powerProduct q m (fun i => x i * h i) * (powerProduct q m h)⁻¹) := by
  simp only [powerProduct_eq_ordered, cosetChange_mul, paperConj_pow]
  rw [conjugated_product_collection]
  exact mul_assoc _ _ _

/-- The ambient element inducing the paper's corrected automorphism `kᵢ`.
It is `hᵢ^{-τᵢ(h)}`, not `hᵢ^{τᵢ(h)}`. -/
def correctedElement (q : ℕ) {m : ℕ} (h : Fin m → G) (i : Fin m) : G :=
  paperConj (h i)⁻¹ (powerPrefix q h i)

/-- The paper's right action represented in Mathlib's composition convention. -/
def correctedAutomorphisms (N : Subgroup G) [N.Normal] (q : ℕ) {m : ℕ}
    (h : Fin m → G) (i : Fin m) : MulAut N :=
  MulAut.conjNormal (correctedElement q h i)⁻¹

private theorem orderedProduct_mem (H : Subgroup G) {m : ℕ} (f : Fin m → G)
    (hf : ∀ i, f i ∈ H) : orderedProduct f ∈ H := by
  apply H.list_prod_mem
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact hf i

private theorem prefix_conjugates_generate (q m : ℕ) (h : Fin m → G) :
    Subgroup.closure (Set.range (fun i => paperConj (h i) (powerPrefix q h i))) =
      Subgroup.closure (Set.range h) := by
  induction m with
  | zero => simp [Set.range_eq_empty]
  | succ m ih =>
    let H := Subgroup.closure (Set.range h)
    let K := Subgroup.closure
      (Set.range (fun i => paperConj (h i) (powerPrefix q h i)))
    let H₀ := Subgroup.closure (Set.range (fun i : Fin m => h i.castSucc))
    have hH₀ : H₀ ≤ H := Subgroup.closure_mono (by
      rintro z ⟨i, rfl⟩
      exact ⟨i.castSucc, rfl⟩)
    have hK₀ : H₀ ≤ K := by
      dsimp only [H₀]
      rw [← ih (fun i => h i.castSucc)]
      apply (Subgroup.closure_le _).mpr
      rintro z ⟨i, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨i.castSucc, ?_⟩
      simp only [powerPrefix, prefixProduct_castSucc]
    let R := orderedProduct (fun i : Fin m => h i.castSucc ^ q)
    have hR : R ∈ H₀ := orderedProduct_mem H₀ _ (fun i =>
      H₀.pow_mem (Subgroup.subset_closure ⟨i, rfl⟩) q)
    have hlast : paperConj (h (Fin.last m)) (powerPrefix q h (Fin.last m)) =
        R * h (Fin.last m) * R⁻¹ := by
      simp only [powerPrefix, prefixProduct_last, paperConj, inv_inv]
      rfl
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro z ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change paperConj (h (Fin.last m)) (powerPrefix q h (Fin.last m)) ∈ H
        rw [hlast]
        exact H.mul_mem (H.mul_mem (hH₀ hR) (Subgroup.subset_closure
          ⟨Fin.last m, rfl⟩)) (H.inv_mem (hH₀ hR))
      · apply hH₀
        change paperConj (h j.castSucc) (powerPrefix q h j.castSucc) ∈
          Subgroup.closure (Set.range (fun i : Fin m => h i.castSucc))
        rw [← ih (fun i => h i.castSucc)]
        apply Subgroup.subset_closure
        refine ⟨j, ?_⟩
        simp only [powerPrefix, prefixProduct_castSucc]
    · apply (Subgroup.closure_le _).mpr
      rintro z ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change h (Fin.last m) ∈ K
        have hk : R * h (Fin.last m) * R⁻¹ ∈ K :=
          hlast ▸ Subgroup.subset_closure ⟨Fin.last m, rfl⟩
        have hh := K.mul_mem (K.mul_mem (K.inv_mem (hK₀ hR)) hk) (hK₀ hR)
        have he : R⁻¹ * (R * h (Fin.last m) * R⁻¹) * R = h (Fin.last m) := by group
        exact he ▸ hh
      · exact hK₀ (Subgroup.subset_closure ⟨j, rfl⟩)

/-- The corrected automorphisms generate precisely the original prescribed
action group. In particular they preserve its orbits and its transitivity. -/
theorem correctedAutomorphisms_generated (N : Subgroup G) [N.Normal]
    (q m : ℕ) (h : Fin m → G) :
    Subgroup.closure (Set.range (correctedAutomorphisms N q h)) =
      Subgroup.closure (Set.range (fun i => (MulAut.conjNormal (h i) : MulAut N))) := by
  have hgen := congrArg (fun H : Subgroup G => H.map (MulAut.conjNormal : G →* MulAut N))
    (prefix_conjugates_generate q m h)
  simp only [MonoidHom.map_closure, ← Set.range_comp, Function.comp_def] at hgen
  have he : correctedAutomorphisms N q h =
      fun i => (MulAut.conjNormal (paperConj (h i) (powerPrefix q h i)) : MulAut N) := by
    funext i
    simp [correctedAutomorphisms, correctedElement, paperConj, mul_assoc]
  rw [he]
  exact hgen

/-- Proposition 10.2's actual ordered commutator-value-set coverage input.
The inner corrections are chosen before the arbitrary target. In the paper's
right-action convention, `yᵢ kᵢ` acts as `kᵢ * conj(yᵢ⁻¹)` in Mathlib.
There is no assertion about joins or generated commutator subgroups here. -/
def PrescribedCommutatorCoverage (A : Type*) [Group A] (q m : ℕ)
    (k : Fin m → MulAut A) : Prop :=
  ∃ y : Fin m → A, ∀ t : A, ∃ c : Fin m → A,
    orderedProduct (fun i => (c i)⁻¹ *
      ((k i * MulAut.conj (y i)⁻¹) ^ q) (c i)) = t

private theorem quotient_coset_powerProduct (N : Subgroup G) [N.Normal]
    (q m : ℕ) (x : Fin m → N) (h : Fin m → G) :
    QuotientGroup.mk' N (powerProduct q m (fun i => (x i : G) * h i)) =
      QuotientGroup.mk' N (powerProduct q m h) := by
  simp only [map_powerProduct, map_mul]
  congr 1
  funext i
  rw [show QuotientGroup.mk' N (x i : G) = 1 from
    (QuotientGroup.eq_one_iff _).mpr (x i).property, one_mul]

/-- The recursive triangular substitution on p. 228. Every chosen `yᵢ` is
realized exactly, including its inner action, by a coset element `xᵢ hᵢ`.
The prefix at position `i` depends only on the earlier `xⱼ`. -/
theorem triangular_transport (N : Subgroup G) [N.Normal] (q m : ℕ)
    (h : Fin m → G) (y : Fin m → N) :
    ∃ x : Fin m → N, ∀ i,
      paperConj (((x i : G) * h i)⁻¹)
          (powerPrefix q (fun j => (x j : G) * h j) i) =
        (y i : G) * correctedElement q h i := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨x, hx⟩ := ih (fun i => h i.castSucc) (fun i => y i.castSucc)
    let P := powerProduct q m (fun i => (x i : G) * h i.castSucc)
    let R := powerProduct q m (fun i => h i.castSucc)
    have hquot : QuotientGroup.mk' N P = QuotientGroup.mk' N R := by
      exact quotient_coset_powerProduct N q m x (fun i => h i.castSucc)
    have hξ : P⁻¹ * R ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (P⁻¹ * R) = 1
      rw [map_mul, map_inv, hquot, inv_mul_cancel]
    let ξ : N := ⟨P⁻¹ * R, hξ⟩
    let xl : N := ξ * MulAut.conjNormal (h (Fin.last m))
      (MulAut.conjNormal R⁻¹ ((y (Fin.last m))⁻¹) * ξ⁻¹)
    refine ⟨Fin.snoc x xl, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [powerPrefix, prefixProduct_last, Fin.snoc_castSucc, Fin.snoc_last,
        correctedElement]
      simp only [← powerProduct_eq_ordered]
      change paperConj (((xl : G) * h (Fin.last m))⁻¹) P⁻¹ =
        (y (Fin.last m) : G) * paperConj (h (Fin.last m))⁻¹ R⁻¹
      simp only [xl, ξ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        paperConj]
      group
    · simpa only [powerPrefix, prefixProduct_castSucc, Fin.snoc_castSucc,
        correctedElement] using hx j

private theorem commutator_transport (N : Subgroup G) [N.Normal]
    (q : ℕ) (u τ : G) (c : N) :
    paperConj (paperComm (MulAut.conjNormal τ c : G) (u ^ q)⁻¹) τ =
      ((c⁻¹ * ((MulAut.conjNormal (paperConj u⁻¹ τ)⁻¹ : MulAut N) ^ q) c : N) : G) := by
  rw [← map_pow]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
  have hp : (paperConj u⁻¹ τ)⁻¹ ^ q = paperConj (u ^ q) τ := by
    rw [← paperConj_pow]
    simp [paperConj, ← mul_assoc]
  rw [hp]
  simp only [paperConj, paperComm]
  group

/-- The exact prescribed-coset conclusion of Proposition 10.1, conditional
only on the independent ordered commutator-value coverage of Proposition 10.2
for its corrected prescribed automorphisms. No finiteness or width bound is
needed in this purely algebraic reduction; `q` and `m` are preserved exactly. -/
theorem coset_power_surjective_of_prescribed_commutator_coverage
    (N : Subgroup G) [N.Normal] (q m : ℕ) (h : Fin m → G)
    (coverage : PrescribedCommutatorCoverage N q m (correctedAutomorphisms N q h))
    (a : N) :
    ∃ b : Fin m → N,
      powerProduct q m (fun i => (b i : G) * h i) =
        (a : G) * powerProduct q m h := by
  obtain ⟨y, hy⟩ := coverage
  obtain ⟨x, hx⟩ := triangular_transport N q m h y
  let P := powerProduct q m (fun i => (x i : G) * h i)
  let R := powerProduct q m h
  have hψ : P * R⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (P * R⁻¹) = 1
    rw [map_mul, map_inv, quotient_coset_powerProduct N q m x h, mul_inv_cancel]
  let ψ : N := ⟨P * R⁻¹, hψ⟩
  obtain ⟨c, hc⟩ := hy (a * ψ⁻¹)
  let τ := powerPrefix q (fun i => (x i : G) * h i)
  let d : Fin m → N := fun i => MulAut.conjNormal (τ i) (c i)
  have haction (i : Fin m) :
      correctedAutomorphisms N q h i * MulAut.conj (y i)⁻¹ =
        MulAut.conjNormal (paperConj (((x i : G) * h i)⁻¹) (τ i))⁻¹ := by
    rw [hx i]
    simp only [correctedAutomorphisms, mul_inv_rev, map_mul, map_inv,
      MulAut.conjNormal_val]
  have hcomm : orderedProduct (fun i =>
      paperConj (paperComm (d i : G) (((x i : G) * h i) ^ q)⁻¹) (τ i)) =
        (a : G) * (P * R⁻¹)⁻¹ := by
    simp_rw [d, commutator_transport, ← haction]
    have ht := congrArg N.subtype hc
    rw [map_orderedProduct] at ht
    exact ht
  let b : Fin m → N := fun i =>
    MulAut.conjNormal (d i : G)⁻¹ (x i) *
      (d i)⁻¹ * MulAut.conjNormal (h i) (d i)
  have hb (i : Fin m) : (b i : G) =
      cosetChange (fun j => (x j : G)) (fun j => (d j : G)) h i := by
    simp only [b, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
      cosetChange, paperConj, paperComm]
    group
  refine ⟨b, ?_⟩
  have heq := equation43 q m (fun i => (x i : G)) (fun i => (d i : G)) h
  simp_rw [← hb] at heq
  rw [hcomm] at heq
  change powerProduct q m (fun i => (b i : G) * h i) * R⁻¹ =
    (a : G) * (P * R⁻¹)⁻¹ * (P * R⁻¹) at heq
  have := congrArg (fun z : G => z * R) heq
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one] using this

end NikolovSegal
