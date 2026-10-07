/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3BareOrbital
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3BareOrbital
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3FieldReconstruction
import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3ModelCorrections

set_option autoImplicit false
set_option maxHeartbeats 1800000
/-! Actual bare-projective A2 orbital PRODUCT for Nikolov--Segal Part II
p260. The genuine quotient model is used only ON U, with derived invariance
of every corrected model step. Actual projective corrections precede targets;
no bare-auto lift or whole-block coverage hypothesis is assumed. -/
namespace NikolovSegal.PartIIPSL3BareOrbital
open PartIIPSL3Unipotent PartIIPSL3FieldReconstruction PartIIPSL3ModelCorrections
open PartIIA2Orbital PartIIA2GraphSupply Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev pi : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (Subgroup.center _)
private theorem model_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (alpha : Fin 3 → Fin M → MulAut PSL(3,F))
    (a : Fin 3 → Fin M → Fin 3 → Fˣ) (phi : Fin 3 → Fin M → RingAut F)
    (eps : Fin 3 → Fin M → Bool)
    (hm : ∀ r j z, z ∈ upperUnipotent (F := F) →
      alpha r j (pi z)=pi (diagonalFieldGraphAut (a r j) (phi r j) (eps r j) z))
    (e : Fin 3 → Fin M → ℕ) (he : ∀ r j, 0 < e r j ∧ e r j ∣ q) :
    ∃ y : Fin 3 → Fin M → PSL(3,F), ∀ target ∈ projectiveUpperUnipotent (F := F),
      ∃ c : Fin 3 → Fin M → PSL(3,F), (∀ r j, c r j ∈ projectiveUpperUnipotent) ∧
        orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M => (c r j)⁻¹ *
          (((alpha r j*MulAut.conj (y r j)⁻¹)^(q/e r j)) (c r j))))=target := by
  classical
  obtain ⟨ym,hpres,hcover⟩ := actual_normalizing_A2_model_orbital_product hq hM hF a phi eps e he
  let model := fun r j => diagonalFieldGraphAut (a r j) (phi r j) (eps r j)
  let y := fun r j => (alpha r j).symm (pi (model r j (ym r j)))
  let gamma := fun r j => model r j*MulAut.conj (ym r j)⁻¹
  have hstep : ∀ r j z, z ∈ upperUnipotent (F := F) →
      (alpha r j*MulAut.conj (y r j)⁻¹) (pi z)=pi (gamma r j z) := by
    intro r j z hz
    simp only [y,gamma,MulAut.mul_apply,MulAut.conj_inv_apply,map_mul,map_inv,
      MulEquiv.apply_symm_apply]
    rw [hm r j z hz]
  have hpow : ∀ r j n z, z ∈ upperUnipotent (F := F) →
      ((alpha r j*MulAut.conj (y r j)⁻¹)^n) (pi z)=pi ((gamma r j^n) z) := by
    intro r j n
    induction n with
    | zero => intro z hz; rfl
    | succ n ih =>
      intro z hz
      rw [pow_succ',MulAut.mul_apply,ih z hz,pow_succ',MulAut.mul_apply]
      exact hstep r j _ ((a2Actual% power_preserves_U) (gamma r j) (hpres r j) n z hz)
  refine ⟨y,?_⟩
  intro target ht
  obtain ⟨z,hz,rfl⟩ := ht
  obtain ⟨c,hc,hval⟩ := hcover z hz
  refine ⟨fun r j => pi (c r j),fun r j => Subgroup.mem_map_of_mem pi (hc r j),?_⟩
  have hvalues : ∀ r j, pi ((c r j)⁻¹*((gamma r j)^(q/e r j)) (c r j))=
      (pi (c r j))⁻¹*(((alpha r j*MulAut.conj (y r j)⁻¹)^(q/e r j)) (pi (c r j))) := by
    intro r j
    rw [map_mul,map_inv,← hpow r j _ _ (hc r j)]
  have hh := congrArg pi hval
  simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def] at hh
  change orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M =>
    pi ((c r j)⁻¹*((gamma r j)^(q/e r j)) (c r j))))=pi z at hh
  simp_rw [hvalues] at hh
  exact hh

/-- Genuine arbitrary-bare-PSL3 orbital PRODUCT. ONE actual projective
correction tuple is fixed before every target, using the actual U model and
corrected q/e power transport. No lift/root-image/coverage premise. -/
theorem actual_bare_PSL3_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin 3 → Fin M → MulAut PSL(3,F))
    (e : Fin 3 → Fin M → ℕ) (he : ∀ r j, 0 < e r j ∧ e r j ∣ q) :
    ∃ y : Fin 3 → Fin M → PSL(3,F), ∀ target ∈ projectiveUpperUnipotent (F := F),
      ∃ c : Fin 3 → Fin M → PSL(3,F), (∀ r j, c r j ∈ projectiveUpperUnipotent) ∧
        orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M => (c r j)⁻¹ *
          (((beta r j*MulAut.conj (y r j)⁻¹)^(q/e r j)) (c r j))))=target := by
  classical
  have hsize : 4 < Fintype.card F := lt_of_le_of_lt
    (by have hh : 1 ≤ (4*q+1)^q := Nat.one_le_pow q _ (by omega); omega) hF
  choose g a phi eps hm using fun r j => actual_bare_PSL3_U_action_model hsize (beta r j)
  let alpha := fun r j => MulAut.conj (g r j)⁻¹*beta r j
  obtain ⟨y,hy⟩ := model_orbital_product hq hM hF alpha a phi eps hm e he
  let x := fun r j => y r j*(beta r j).symm (g r j)
  have hx : ∀ r j, beta r j*MulAut.conj (x r j)⁻¹=alpha r j*MulAut.conj (y r j)⁻¹ := by
    intro r j
    apply MulEquiv.ext; intro z
    dsimp only [alpha]
    simp only [MulAut.mul_apply,MulAut.conj_apply,inv_inv]
    dsimp only [x]
    simp only [mul_inv_rev,map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  refine ⟨x,?_⟩
  intro target ht
  obtain ⟨c,hc,hprod⟩ := hy target ht
  exact ⟨c,hc,by simpa only [hx] using hprod⟩

private theorem ordered_blocks {M : ℕ} (f : Fin (3*M) → PSL(3,F)) :
    orderedProduct f=orderedProduct (fun k : Fin 3 => orderedProduct
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
/-- The actual three scalar blocks in their increasing original index order. -/
theorem actual_bare_PSL3_ordered_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (beta : Fin (3*M) → MulAut PSL(3,F)) (e : Fin (3*M) → ℕ)
    (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin (3*M) → PSL(3,F), ∀ target ∈ projectiveUpperUnipotent (F := F),
      ∃ c : Fin (3*M) → PSL(3,F), (∀ j, c j ∈ projectiveUpperUnipotent) ∧
        orderedProduct (fun j => (c j)⁻¹ *
          (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j)))=target := by
  classical
  obtain ⟨yb,hyb⟩ := actual_bare_PSL3_orbital_product hq hM hF
    (fun r j => beta (finProdFinEquiv (r,j))) (fun r j => e (finProdFinEquiv (r,j)))
    (fun r j => he _)
  let y := fun j : Fin (3*M) => yb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨y,?_⟩
  intro target ht
  obtain ⟨cb,hmem,hval⟩ := hyb target ht
  let c := fun j : Fin (3*M) => cb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨c,fun j => hmem _ _,?_⟩
  rw [ordered_blocks]
  change orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M =>
    (c (finProdFinEquiv (r,j)))⁻¹ *
      (((beta (finProdFinEquiv (r,j))*MulAut.conj (y (finProdFinEquiv (r,j)))⁻¹)^
        (q/e (finProdFinEquiv (r,j)))) (c (finProdFinEquiv (r,j))))))=target
  simpa only [c,y,Equiv.symm_apply_apply] using hval
end NikolovSegal.PartIIPSL3BareOrbital
