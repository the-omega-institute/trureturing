/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2ScalarSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2ScalarSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2BareOrbital
import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentWidth
import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoordinates
import D5.S3.FiniteGroups.NikolovSegal.PartIILemma41
set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! Nikolov--Segal Part II section 6: actual rank-two global assembly.
The proved bare-auto U orbital product is transported to literal lower U,
then the accepted all-field Fin25 alternating decomposition is consumed.
No scalar coverage, decomposition or automorphism-classification premise. -/
open Lean Elab Term in
elab "sl3Width%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIISL3UnipotentWidthGeometry"
  let suffix := ".NikolovSegal.PartIISL3UnipotentWidth." ++ id.getId.toString
  let chosen := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ owner
  match chosen with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique proved SL3 width kernel {id} not found"
namespace NikolovSegal.PartIIA2ScalarSupply
open PartIIA2Orbital PartIIA2BareOrbital PartIISL3UnipotentWidth
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem inverseTranspose_twice (g : SL(3,F)) :
    (((g⁻¹).transpose)⁻¹).transpose=g := by
  rw [← (sl3Width% transpose_inv),inv_inv]
  exact Subtype.ext (Matrix.transpose_transpose _)

private def opposition : MulAut SL(3,F) where
  toFun g := (g⁻¹).transpose
  invFun g := (g⁻¹).transpose
  left_inv := inverseTranspose_twice
  right_inv := inverseTranspose_twice
  map_mul' g h := by
    change ((g*h)⁻¹).transpose=(g⁻¹).transpose*(h⁻¹).transpose
    rw [mul_inv_rev,(sl3Width% transpose_mul)]

private theorem opposition_U (g : SL(3,F)) (hg : g ∈ upperUnipotent (F := F)) :
    opposition g ∈ lowerUnipotent (F := F) := by
  change (g⁻¹).transpose.transpose ∈ upperUnipotent
  have h : (g⁻¹).transpose.transpose=g⁻¹ := Subtype.ext (Matrix.transpose_transpose _)
  rw [h]
  exact upperUnipotent.inv_mem hg

private theorem opposition_lower (g : SL(3,F)) (hg : g ∈ lowerUnipotent (F := F)) :
    opposition.symm g ∈ upperUnipotent (F := F) := by
  change (g⁻¹).transpose ∈ upperUnipotent
  rw [(sl3Width% transpose_inv)]
  exact upperUnipotent.inv_mem hg

private theorem actual_bare_SL3_lower_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin (3*M) → MulAut SL(3,F)) (e : Fin (3*M) → ℕ)
    (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin (3*M) → SL(3,F), ∀ target ∈ lowerUnipotent (F := F),
      ∃ c : Fin (3*M) → SL(3,F), (∀ j, c j ∈ lowerUnipotent) ∧
        orderedProduct (fun j => (c j)⁻¹ *
          (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j)))=target := by
  let T : MulAut SL(3,F) := opposition
  let beta' := fun j => T⁻¹*beta j*T
  obtain ⟨y,hy⟩ := actual_bare_SL3_ordered_orbital_product hq hM hF beta' e he
  have hstep : ∀ j z, (beta j*MulAut.conj (T (y j))⁻¹) (T z)=
      T ((beta' j*MulAut.conj (y j)⁻¹) z) := by
    intro j z
    simp only [beta',MulAut.mul_apply,MulAut.conj_inv_apply,map_mul,map_inv,
      MulAut.apply_inv_self]
  have hpow : ∀ j n z, ((beta j*MulAut.conj (T (y j))⁻¹)^n) (T z)=
      T (((beta' j*MulAut.conj (y j)⁻¹)^n) z) := by
    intro j n z
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',MulAut.mul_apply,ih,hstep]
      exact congrArg T (by rw [pow_succ']; rfl)
  refine ⟨fun j => T (y j),?_⟩
  intro target ht
  obtain ⟨c,hc,hval⟩ := hy (T.symm target) (opposition_lower target ht)
  refine ⟨fun j => T (c j),fun j => opposition_U _ (hc j),?_⟩
  have hm : ∀ f : Fin (3*M) → SL(3,F), T (orderedProduct f)=orderedProduct (fun j => T (f j)) := by
    intro f
    simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]
  have hv : ∀ j, T ((c j)⁻¹*(((beta' j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j)))=
      (T (c j))⁻¹*(((beta j*MulAut.conj (T (y j))⁻¹)^(q/e j)) (T (c j))) := by
    intro j
    rw [map_mul,map_inv,← hpow]
  have hprod := congrArg T hval
  rw [hm,MulEquiv.apply_symm_apply] at hprod
  simpa only [hv] using hprod

private theorem ordered_25_blocks {M : ℕ} (f : Fin (25*M) → SL(3,F)) :
    orderedProduct f=orderedProduct (fun k : Fin 25 => orderedProduct
      (fun j : Fin M => f (finProdFinEquiv (k,j)))) := by
  simp only [orderedProduct,List.ofFn_mul,List.prod_flatten,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  simp only [finProdFinEquiv]
  ac_rfl

/-- Full SL3 scalar PRODUCT for ALL prescribed bare automorphisms, original
q/e divisor powers and ALL full-group targets. ONE correction tuple precedes
all targets. The exact length is 25*(3*M); neither M nor the field cutoff
depends on any automorphism, divisor tuple or target. -/
theorem actual_SL3_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin (25*(3*M)) → MulAut SL(3,F)) (e : Fin (25*(3*M)) → ℕ) :
    PartIIScalarProductInput q (25*(3*M)) beta e := by
  classical
  intro he
  let b := fun (k : Fin 25) (j : Fin (3*M)) => finProdFinEquiv (k,j)
  have hblocks : ∀ k : Fin 25, ∃ y : Fin (3*M) → SL(3,F),
      ∀ target ∈ (if Even k.val then upperUnipotent (F := F) else lowerUnipotent),
      ∃ c : Fin (3*M) → SL(3,F), orderedProduct (fun j => (c j)⁻¹*
        (((beta (b k j)*MulAut.conj (y j)⁻¹)^(q/e (b k j))) (c j)))=target := by
    intro k
    by_cases hk : Even k.val
    · obtain ⟨y,hy⟩ := actual_bare_SL3_ordered_orbital_product hq hM hF
        (fun j => beta (b k j)) (fun j => e (b k j)) (fun j => he _)
      refine ⟨y,?_⟩
      intro target ht
      obtain ⟨c,_,hc⟩ := hy target (by simpa only [if_pos hk] using ht)
      exact ⟨c,hc⟩
    · obtain ⟨y,hy⟩ := actual_bare_SL3_lower_orbital_product hq hM hF
        (fun j => beta (b k j)) (fun j => e (b k j)) (fun j => he _)
      refine ⟨y,?_⟩
      intro target ht
      obtain ⟨c,_,hc⟩ := hy target (by simpa only [if_neg hk] using ht)
      exact ⟨c,hc⟩
  choose y hy using hblocks
  let x := fun j : Fin (25*(3*M)) => y (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨x,?_⟩
  intro target
  obtain ⟨u,hu,hprod⟩ := alternating_unipotent_25 target
  have humem : ∀ k, u k ∈ (if Even k.val then upperUnipotent (F := F) else lowerUnipotent) := by
    intro k
    by_cases hk : Even k.val <;> simpa only [hk,if_true,if_false] using hu k
  choose c hc using fun k => hy k (u k) (humem k)
  let call := fun j : Fin (25*(3*M)) => c (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨call,?_⟩
  rw [ordered_25_blocks]
  simp only [call,x,Equiv.symm_apply_apply]
  have hval := congrArg orderedProduct (funext hc)
  exact hval.trans hprod

/-- Uniform quantitative SL3-family length/cutoff, chosen BEFORE every
finite field, bare automorphism tuple, divisor tuple and target. This is
rank-two family supply, not all-simple exhaustion or the full supplier. -/
theorem actual_SL3_uniform_scalar_product (q : ℕ) (hq : 0 < q) :
    ∃ N C : ℕ, 0 < N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C < Fintype.card F → ∀ (beta : Fin N → MulAut SL(3,F)) (e : Fin N → ℕ),
        PartIIScalarProductInput q N beta e := by
  let M := q*(4*q+1)+1
  refine ⟨25*(3*M),4*(4*q+1)^q,by dsimp only [M]; positivity,?_⟩
  intro F _ _ _ hF beta e
  exact actual_SL3_scalar_product hq (by dsimp only [M]; omega) hF beta e

private theorem SL3_card_bound [Fintype F] : Nat.card SL(3,F) ≤ Fintype.card F^9 := by
  classical
  have h : Nat.card SL(3,F) ≤ Nat.card (Matrix (Fin 3) (Fin 3) F) :=
    Nat.card_le_card_of_injective (fun g : SL(3,F) => g.val) Subtype.val_injective
  calc
    _ ≤ Nat.card (Matrix (Fin 3) (Fin 3) F) := h
    _ = Fintype.card F^9 := by
      simp [Nat.card_eq_fintype_card,Matrix,Fintype.card_fun,← pow_mul]

/-- Proved SL3 q=1 scalar supply, consumed in the original Lemma4.1 algebra:
actual twisted PRODUCT of absolute length450 for every field of card>20. -/
theorem actual_SL3_twisted_product [Fintype F] [DecidableEq F]
    (hF : 20 < Fintype.card F) : Equation47WordCoupling.PartIITwistedProductInput SL(3,F) 450 := by
  apply twisted_input_of_scalar_one
  intro beta
  exact actual_SL3_scalar_product (q := 1) (M := 6)
    (by decide) (by decide) (by simpa using hF) beta (fun _ => 1)

/-- Unconditional SL3-family realization of the original prescribed factor
coverage, with length and GROUP cutoff fixed before all finite fields,
ranks, actual action tuples and targets. Powered components, the actual
Hall selections and the same pre-target correction are supplied by the
accepted mixed reconstruction. All-simple exhaustion is still unproved. -/
theorem uniform_SL3_transitive_coverage (q : ℕ) (hq : 0 < q) :
    ∃ m C : ℕ, 0 < m ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C < Nat.card SL(3,F) → ∀ (I : Type u) [Finite I] [Nonempty I],
      ∀ (k : Fin m → MulAut (I → SL(3,F))) (sigma : Fin m → Equiv.Perm I)
        (beta : Fin m → I → MulAut SL(3,F)),
      (∀ j z i, k j z (sigma j i)=beta j i (z i)) →
      PrescribedCommutatorCoverage (I → SL(3,F)) q m k := by
  let M := 25*(3*(q*(4*q+1)+1))
  let K := 4*(4*q+1)^q
  let m := M*904*(q+904)
  refine ⟨m,max (K^9) (20^9),by dsimp only [m,M]; positivity,?_⟩
  intro F _ _ _ hcard I _ _ k sigma beta hcoord
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hfield : ∀ A : ℕ, A^9 < Nat.card SL(3,F) → A < Fintype.card F := by
    intro A ha
    by_contra hn
    have hb : Nat.card SL(3,F) ≤ Fintype.card F^9 := SL3_card_bound
    exact (not_lt_of_ge (hb.trans (Nat.pow_le_pow_left (Nat.le_of_not_gt hn) 9))) ha
  have hfq : K < Fintype.card F := hfield K ((le_max_left _ _).trans_lt hcard)
  have hf1 : 20 < Fintype.card F := hfield 20 ((le_max_right _ _).trans_lt hcard)
  exact prescribed_coverage_from_published_products (M := M) (D := 450) hq
    (by dsimp only [M]; positivity) (by dsimp only [m]; norm_num)
    k sigma beta hcoord
    (fun b e => actual_SL3_scalar_product hq (by omega) hfq b e)
    (actual_SL3_twisted_product hf1)
end NikolovSegal.PartIIA2ScalarSupply
