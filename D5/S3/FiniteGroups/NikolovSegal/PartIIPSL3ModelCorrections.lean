/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3ModelCorrections
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3ModelCorrections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2BareOrbital

set_option autoImplicit false
set_option maxHeartbeats 1800000
/-! Nikolov--Segal Part II p260 height filtration in the projective consumer.
The accepted A2 arithmetic is reused, retaining the constructed correction's
actual U invariance which is needed for projective q/e power transport. -/
open Lean Elab Term in
elab "psl3Model%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIA2GraphSupply"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ owner
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique accepted A2 model kernel {id} not found"
namespace NikolovSegal.PartIIPSL3ModelCorrections
open PartIIA2Orbital PartIIA2GraphSupply PartIIA2GraphTorus Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev block2 {M : ℕ} (i : Fin 2) (j : Fin M) := finProdFinEquiv (i,j)
private theorem donor_block2_eq {M : ℕ} (i : Fin 2) (j : Fin M) :
    (a2Actual% block2) i j=block2 i j := rfl
private theorem actual_normalizing_central_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin M → Fin 3 → Fˣ) (phi : Fin M → RingAut F) (eps : Fin M → Bool)
    (e : Fin M → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin M → SL(3,F),
      (∀ j z, z ∈ upperUnipotent (F := F) →
        (diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹) z ∈ upperUnipotent) ∧
      ∀ target : F, ∃ t : Fin M → F,
      orderedProduct (fun j => (transvection (show (0:Fin 3) ≠ 2 by decide) (t j))⁻¹*
        (((diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹)^(q/e j))
          (transvection (show (0:Fin 3) ≠ 2 by decide) (t j)))) =
        transvection (show (0:Fin 3) ≠ 2 by decide) target := by
  let beta := fun j => diagonalFieldGraphAut (a j) (phi j) (eps j)
  let chi := fun j => if eps j then -((a j 0:F)*(↑(a j 2)⁻¹:F))
      else (a j 0:F)*(↑(a j 2)⁻¹:F)
  have hchi : ∀ j, chi j ≠ 0 := by
    intro j; dsimp [chi]; split_ifs
    · exact neg_ne_zero.mpr (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    · exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have hbeta : ∀ j t, beta j (transvection (show (0:Fin 3) ≠ 2 by decide) t) =
      transvection (show (0:Fin 3) ≠ 2 by decide) (chi j*phi j t) := by
    intro j t
    cases hs : eps j
    · simp only [beta,chi,hs,Bool.false_eq_true,ite_false,diagonalFieldGraphAut,mul_one]
      rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    · simp only [beta,chi,hs,ite_true,diagonalFieldGraphAut,MulAut.mul_apply]
      rw [tau_T02,diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root),map_neg]
      congr 1
      ring
  let H : Fin M → (l : F) → l ≠ 0 → SL(3,F) :=
    fun _ l hl => diag2n (show (0:Fin 3) ≠ 2 by decide) l hl
  have hcycle : ∀ j l hl t, ((MulAut.conj (H j l hl)*beta j)^1)
      (transvection (show (0:Fin 3) ≠ 2 by decide) t)=
        transvection (show (0:Fin 3) ≠ 2 by decide) (chi j*l^2*phi j t) := by
    intro j l hl t
    rw [pow_one,MulAut.mul_apply,hbeta]
    dsimp only [H]
    rw [(a2Kernel% diag2n_root)]
    congr 1
    ring
  obtain ⟨l,hl,y,hy,hcover⟩ := (psl3Model% actual_root_cycle_product)
    (show (0:Fin 3) ≠ 2 by decide) hq hM hF beta H (fun _ => 1) (fun _ => 2)
    (by intro j; omega) phi chi hchi e he hcycle
  refine ⟨y,?_,?_⟩
  · intro j z hz
    rw [hy j,MulAut.mul_apply]
    exact (a2Actual% diag2n_preserves_U) (show (0:Fin 3) ≠ 2 by decide) (l j) (hl j) _
      ((a2Actual% beta_preserves_U) (a j) (phi j) (eps j) z hz)
  · intro target
    simpa only [one_mul] using hcover target
theorem actual_normalizing_A2_model_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin 3 → Fin M → Fin 3 → Fˣ) (phi : Fin 3 → Fin M → RingAut F)
    (eps : Fin 3 → Fin M → Bool) (e : Fin 3 → Fin M → ℕ)
    (he : ∀ r j, 0 < e r j ∧ e r j ∣ q) :
    ∃ y : Fin 3 → Fin M → SL(3,F),
      (∀ r j z, z ∈ upperUnipotent (F := F) →
        (diagonalFieldGraphAut (a r j) (phi r j) (eps r j)*MulAut.conj (y r j)⁻¹) z ∈ upperUnipotent) ∧
      ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin 3 → Fin M → SL(3,F), (∀ r j, c r j ∈ upperUnipotent) ∧
        orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M => (c r j)⁻¹ *
          (((diagonalFieldGraphAut (a r j) (phi r j) (eps r j)*MulAut.conj (y r j)⁻¹)^(q/e r j))
            (c r j)))) = target := by
  classical
  obtain ⟨l0,hl0,y0,hy0,hcover0⟩ := actual_mixed_graph_root01_product hq hM hF
    (a 0) (phi 0) (eps 0) (e 0) (he 0)
  obtain ⟨l1,hl1,y1,hy1,hcover1⟩ := actual_mixed_graph_root12_product hq hM hF
    (a 1) (phi 1) (eps 1) (e 1) (he 1)
  obtain ⟨y2,hpres2,hcover2⟩ := actual_normalizing_central_product hq hM hF
    (a 2) (phi 2) (eps 2) (e 2) (he 2)
  let beta := fun r j => diagonalFieldGraphAut (a r j) (phi r j) (eps r j)
  let g0 := fun j => (beta 0 j*MulAut.conj (y0 j)⁻¹)^(q/e 0 j)
  let g1 := fun j => (beta 1 j*MulAut.conj (y1 j)⁻¹)^(q/e 1 j)
  have hpres0 : ∀ j g, g ∈ upperUnipotent → g0 j g ∈ upperUnipotent := by
    intro j
    apply (a2Actual% power_preserves_U)
    intro g hg
    rw [hy0 j,MulAut.mul_apply]
    have hb := (a2Actual% beta_preserves_U) (a 0 j) (phi 0 j) (eps 0 j) g hg
    cases hs : eps 0 j
    · simpa only [hs,Bool.false_eq_true,ite_false] using (a2Actual% diag2n_preserves_U)
        (show (0:Fin 3) ≠ 1 by decide) (l0 j) (hl0 j) _ hb
    · simpa only [hs,ite_true] using (a2Actual% H_preserves_U) (l0 j) (hl0 j) _ hb
  have hpres1 : ∀ j g, g ∈ upperUnipotent → g1 j g ∈ upperUnipotent := by
    intro j
    apply (a2Actual% power_preserves_U)
    intro g hg
    rw [hy1 j,MulAut.mul_apply]
    have hb := (a2Actual% beta_preserves_U) (a 1 j) (phi 1 j) (eps 1 j) g hg
    cases hs : eps 1 j
    · simpa only [hs,Bool.false_eq_true,ite_false] using (a2Actual% diag2n_preserves_U)
        (show (1:Fin 3) ≠ 2 by decide) (l1 j) (hl1 j) _ hb
    · simpa only [hs,ite_true] using (a2Actual% mirrored_H_preserves_U) (l1 j) (hl1 j) _ hb
  let G : Fin 2 → Fin M → MulAut SL(3,F) := ![g0,g1]
  let gamma : Fin (2*M) → MulAut SL(3,F) := fun k => G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hG : ∀ r j g, g ∈ upperUnipotent → G r j g ∈ upperUnipotent := by
    intro r j g hg
    fin_cases r
    · exact hpres0 j g hg
    · exact hpres1 j g hg
  have hgamma : ∀ k g, g ∈ upperUnipotent → gamma k g ∈ upperUnipotent := by
    intro k g hg
    exact hG _ _ g hg
  let y : Fin 3 → Fin M → SL(3,F) := ![y0,y1,y2]
  refine ⟨y,?_,?_⟩
  · intro i j z hz
    dsimp only [y]
    fin_cases i
    · change (diagonalFieldGraphAut (a 0 j) (phi 0 j) (eps 0 j)*MulAut.conj (y0 j)⁻¹) z ∈ upperUnipotent
      rw [hy0 j,MulAut.mul_apply]
      have hb := (a2Actual% beta_preserves_U) (a 0 j) (phi 0 j) (eps 0 j) z hz
      cases hs : eps 0 j
      · simpa only [hs,Bool.false_eq_true,ite_false] using (a2Actual% diag2n_preserves_U)
          (show (0:Fin 3) ≠ 1 by decide) (l0 j) (hl0 j) _ hb
      · simpa only [hs,ite_true] using (a2Actual% H_preserves_U) (l0 j) (hl0 j) _ hb
    · change (diagonalFieldGraphAut (a 1 j) (phi 1 j) (eps 1 j)*MulAut.conj (y1 j)⁻¹) z ∈ upperUnipotent
      rw [hy1 j,MulAut.mul_apply]
      have hb := (a2Actual% beta_preserves_U) (a 1 j) (phi 1 j) (eps 1 j) z hz
      cases hs : eps 1 j
      · simpa only [hs,Bool.false_eq_true,ite_false] using (a2Actual% diag2n_preserves_U)
          (show (1:Fin 3) ≠ 2 by decide) (l1 j) (hl1 j) _ hb
      · simpa only [hs,ite_true] using (a2Actual% mirrored_H_preserves_U) (l1 j) (hl1 j) _ hb
    · exact hpres2 j z hz
  intro target ht
  obtain ⟨A,B,C,rfl⟩ := ht
  obtain ⟨t0,ht0⟩ := hcover0 A
  obtain ⟨t1,ht1⟩ := hcover1 B
  let X : Fin 2 → Fin M → SL(3,F) :=
    ![fun j => transvection (show (0:Fin 3) ≠ 1 by decide) (t0 j),
      fun j => transvection (show (1:Fin 3) ≠ 2 by decide) (t1 j)]
  let R : Fin 2 → Fin M → ℕ := ![fun j => if eps 0 j then 2 else 1,fun j => if eps 1 j then 2 else 1]
  let x := fun k : Fin (2*M) => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  let r := fun k : Fin (2*M) => R (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hx : ∀ k, x k ∈ upperUnipotent := by
    intro k
    dsimp only [x]
    rcases finProdFinEquiv.symm k with ⟨i,j⟩
    fin_cases i
    · simpa [X] using (a2Actual% T01_mem) (t0 j)
    · simpa [X] using (a2Actual% T12_mem) (t1 j)
  have ht0' : orderedProduct (fun j => (transvection (show (0:Fin 3) ≠ 1 by decide) (t0 j))⁻¹ *
      ((g0 j)^(if eps 0 j then 2 else 1)) (transvection (show (0:Fin 3) ≠ 1 by decide) (t0 j))) =
        transvection (show (0:Fin 3) ≠ 1 by decide) A := by
    simpa only [g0,beta,← pow_mul,Nat.mul_comm] using ht0
  have ht1' : orderedProduct (fun j => (transvection (show (1:Fin 3) ≠ 2 by decide) (t1 j))⁻¹ *
      ((g1 j)^(if eps 1 j then 2 else 1)) (transvection (show (1:Fin 3) ≠ 2 by decide) (t1 j))) =
        transvection (show (1:Fin 3) ≠ 2 by decide) B := by
    simpa only [g1,beta,← pow_mul,Nat.mul_comm] using ht1
  have hblocks : ∀ i : Fin 2, orderedProduct (fun j : Fin M =>
      (x (block2 i j))⁻¹*(gamma (block2 i j)^r (block2 i j)) (x (block2 i j))) =
      (![transvection (show (0:Fin 3) ≠ 1 by decide) A,
        transvection (show (1:Fin 3) ≠ 2 by decide) B] : Fin 2 → SL(3,F)) i := by
    intro i
    simp only [x,r,gamma,block2,Equiv.symm_apply_apply]
    fin_cases i
    · simpa [X,R,G] using ht0'
    · simpa [X,R,G] using ht1'
  have hhigh : orderedProduct (fun k => (x k)⁻¹*(gamma k^r k) (x k)) = upper3 A B (A*B) := by
    rw [(a2Actual% ordered_two)]
    simp only [donor_block2_eq]
    have hh := congrArg orderedProduct (funext hblocks)
    rw [hh]
    have hmat : transvection (show (0:Fin 3) ≠ 1 by decide) A*
        transvection (show (1:Fin 3) ≠ 2 by decide) B*
        transvection (show (0:Fin 3) ≠ 2 by decide) (A*B-A*B) = upper3 A B (A*B) :=
      (a2Kernel% three_root_product) A B (A*B)
    simpa [orderedProduct,List.ofFn_succ] using hmat
  obtain ⟨cp,hcp,z,hpv⟩ := PartIIA2ExponentDescent.actual_A2_power_value_descent gamma hgamma x hx r
  rw [hhigh] at hpv
  obtain ⟨t2,ht2⟩ := hcover2 (C-A*B-z)
  let c : Fin 3 → Fin M → SL(3,F) :=
    ![fun j => cp (block2 0 j),fun j => cp (block2 1 j),
      fun j => transvection (show (0:Fin 3) ≠ 2 by decide) (t2 j)]
  refine ⟨c,?_,?_⟩
  · intro i j
    fin_cases i
    · exact hcp _
    · exact hcp _
    · exact (a2Actual% T02_mem) _
  · have hpref : orderedProduct (fun k => (cp k)⁻¹*gamma k (cp k)) =
        orderedProduct (fun j => (cp (block2 0 j))⁻¹*g0 j (cp (block2 0 j))) *
          orderedProduct (fun j => (cp (block2 1 j))⁻¹*g1 j (cp (block2 1 j))) := by
      rw [(a2Actual% ordered_two)]
      simp only [donor_block2_eq]
      have hg : ∀ i j, gamma (block2 i j) = G i j := by
        intro i j
        dsimp only [gamma]
        change G (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2=G i j
        rw [Equiv.symm_apply_apply]
      simp_rw [hg]
      simp [orderedProduct,List.ofFn_succ,G]
    have hout : ∀ f : Fin 3 → SL(3,F), orderedProduct f = f 0*f 1*f 2 := by
      intro f
      simp [orderedProduct,List.ofFn_succ,mul_assoc]
    rw [hout]
    change orderedProduct (fun j => (cp (block2 0 j))⁻¹*g0 j (cp (block2 0 j))) *
      orderedProduct (fun j => (cp (block2 1 j))⁻¹*g1 j (cp (block2 1 j))) *
        orderedProduct (fun j => (transvection (show (0:Fin 3) ≠ 2 by decide) (t2 j))⁻¹*
          (((beta 2 j*MulAut.conj (y2 j)⁻¹)^(q/e 2 j))
            (transvection (show (0:Fin 3) ≠ 2 by decide) (t2 j)))) = _
    rw [← hpref,hpv,ht2]
    have hchart : transvection (show (0:Fin 3) ≠ 2 by decide) (C-A*B-z) = upper3 0 0 (C-A*B-z) := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe,Matrix.one_apply]
    rw [hchart,(a2Kernel% upper3_mul),(a2Kernel% upper3_mul)]
    congr 1 <;> ring
end NikolovSegal.PartIIPSL3ModelCorrections
