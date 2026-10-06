/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphReconstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2GraphReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2GraphSupply
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace NikolovSegal.PartIIA2GraphReconstruction
open Matrix.SpecialLinearGroup PartIIA2Orbital PartIIA2GraphSupply
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem U_of_roots (alpha : MulAut SL(3,F))
    (h01 : ∀ t : F, alpha (transvection (show (0:Fin 3) ≠ 1 by decide) t) ∈ upperUnipotent)
    (h12 : ∀ t : F, alpha (transvection (show (1:Fin 3) ≠ 2 by decide) t) ∈ upperUnipotent)
    (h02 : ∀ t : F, alpha (transvection (show (0:Fin 3) ≠ 2 by decide) t) ∈ upperUnipotent) :
    ∀ g, g ∈ upperUnipotent → alpha g ∈ upperUnipotent := by
  rintro g ⟨a,b,c,rfl⟩
  have hh : transvection (show (0:Fin 3) ≠ 1 by decide) a*
    transvection (show (1:Fin 3) ≠ 2 by decide) b*
    transvection (show (0:Fin 3) ≠ 2 by decide) (c-a*b) = upper3 a b c :=
    (a2Kernel% three_root_product) a b c
  rw [← hh,map_mul,map_mul]
  exact upperUnipotent.mul_mem (upperUnipotent.mul_mem (h01 a) (h12 b)) (h02 _)

private theorem T01_mem (t : F) : transvection (show (0:Fin 3) ≠ 1 by decide) t ∈ upperUnipotent :=
  (a2Kernel% root_mem) (0:Fin 3) t
private theorem T12_mem (t : F) : transvection (show (1:Fin 3) ≠ 2 by decide) t ∈ upperUnipotent :=
  (a2Kernel% root_mem) (1:Fin 3) t
private theorem T02_mem (t : F) : transvection (show (0:Fin 3) ≠ 2 by decide) t ∈ upperUnipotent :=
  (a2Kernel% root_mem) (2:Fin 3) t

private theorem tau_preserves_U : ∀ g : SL(3,F), g ∈ upperUnipotent →
    PartIIA2GraphTorus.tau g ∈ upperUnipotent :=
  U_of_roots _ (fun t => by rw [PartIIA2GraphTorus.tau_T01]; exact T12_mem _)
    (fun t => by rw [PartIIA2GraphTorus.tau_T12]; exact T01_mem _)
    (fun t => by rw [PartIIA2GraphTorus.tau_T02]; exact T02_mem _)

private theorem dphi_preserves_U (a : Fin 3 → Fˣ) (phi : RingAut F) :
    ∀ g : SL(3,F), g ∈ upperUnipotent → diagonalFieldAut a phi g ∈ upperUnipotent := by
  apply U_of_roots
  · intro t
    rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    exact T01_mem _
  · intro t
    rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    exact T12_mem _
  · intro t
    rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    exact T02_mem _

private theorem beta_preserves_U (a : Fin 3 → Fˣ) (phi : RingAut F) (eps : Bool) :
    ∀ g : SL(3,F), g ∈ upperUnipotent → diagonalFieldGraphAut a phi eps g ∈ upperUnipotent := by
  intro g hg
  cases eps
  · simpa only [diagonalFieldGraphAut,Bool.false_eq_true,ite_false,mul_one] using dphi_preserves_U a phi g hg
  · change diagonalFieldAut a phi (PartIIA2GraphTorus.tau g) ∈ upperUnipotent
    exact dphi_preserves_U _ _ _ (tau_preserves_U _ hg)

private theorem diagonal_preserves_U (H : SL(3,F)) (D E : Fin 3 → F)
    (hD : H.val = Matrix.diagonal D) (hE : H⁻¹.val = Matrix.diagonal E) :
    ∀ g : SL(3,F), g ∈ upperUnipotent → MulAut.conj H g ∈ upperUnipotent := by
  have hDE : ∀ k, D k*E k = 1 := by
    intro k
    have hh := congrArg (fun g : SL(3,F) => g.val k k) (mul_inv_cancel H)
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one,hD,hE,
      Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply_eq] at hh
    simpa only [Matrix.one_apply,ite_true,eq_self] using hh
  rintro g ⟨a,b,c,rfl⟩
  refine ⟨D 0*a*E 1,D 1*b*E 2,D 0*c*E 2,?_⟩
  apply Subtype.ext
  change (upper3 (D 0*a*E 1) (D 1*b*E 2) (D 0*c*E 2)).val = H.val*(upper3 a b c).val*H⁻¹.val
  rw [hD,hE]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper3,Matrix.diagonal_mul,Matrix.mul_diagonal,hDE]

private theorem H_preserves_U (lambda : F) (hlambda : lambda ≠ 0) :
    ∀ g : SL(3,F), g ∈ upperUnipotent → MulAut.conj (PartIIA2GraphTorus.H lambda hlambda) g ∈ upperUnipotent :=
  diagonal_preserves_U _ _ _ (PartIIA2GraphTorus.H_coe _ _) (PartIIA2GraphTorus.H_inv_coe _ _)

private theorem diag2n_preserves_U {i j : Fin 3} (hij : i ≠ j) (lambda : F) (hlambda : lambda ≠ 0) :
    ∀ g : SL(3,F), g ∈ upperUnipotent → MulAut.conj (diag2n hij lambda hlambda) g ∈ upperUnipotent := by
  apply diagonal_preserves_U _ _ _ (diag2n_coe _ _ _)
  rw [(a2Kernel% diag2n_inverse)]
  exact diag2n_coe _ _ _

private theorem mirrored_H_preserves_U (lambda : F) (hlambda : lambda ≠ 0) :
    ∀ g : SL(3,F), g ∈ upperUnipotent →
      MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda)) g ∈ upperUnipotent := by
  intro g hg
  have he : MulAut.conj (PartIIA2GraphTorus.tau (PartIIA2GraphTorus.H lambda hlambda)) g =
      PartIIA2GraphTorus.tau (MulAut.conj (PartIIA2GraphTorus.H lambda hlambda) (PartIIA2GraphTorus.tau g)) := by
    simp only [MulAut.conj_apply,map_mul,map_inv,PartIIA2GraphTorus.tau_involutive g]
  rw [he]
  exact tau_preserves_U _ (H_preserves_U _ _ _ (tau_preserves_U _ hg))

private theorem power_preserves_U (gamma : MulAut SL(3,F))
    (hgamma : ∀ g, g ∈ upperUnipotent → gamma g ∈ upperUnipotent) (n : ℕ) :
    ∀ g, g ∈ upperUnipotent → (gamma^n) g ∈ upperUnipotent := by
  intro g hg
  induction n with
  | zero => exact hg
  | succ n ih => rw [pow_succ',MulAut.mul_apply]; exact hgamma _ ih

private def block2 {M : ℕ} (r : Fin 2) (j : Fin M) : Fin (2*M) := finProdFinEquiv (r,j)
private theorem ordered_two {M : ℕ} (f : Fin (2*M) → SL(3,F)) :
    orderedProduct f = orderedProduct (fun r : Fin 2 => orderedProduct (fun j : Fin M => f (block2 r j))) := by
  simp only [orderedProduct,List.ofFn_mul,List.prod_flatten,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext r
  dsimp only [Function.comp_apply]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  simp only [block2,finProdFinEquiv]
  ac_rfl

/-- Full ACTUAL nonabelian A2 orbital product for every diagonal/field/graph
sequence. Three increasing blocks reconstruct every allowed target. The
proved graph-cycle field suppliers, actual U invariance, height-one exponent
descent and central scalar correction are all consumed. ONE y precedes ALL
targets; graph span1/2 disappears by genuine quotient descent, while q/e
remains the original scalar exponent. No orbital/whole-block coverage premise. -/
theorem actual_A2_diagonal_field_graph_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin 3 → Fin M → Fin 3 → Fˣ) (phi : Fin 3 → Fin M → RingAut F)
    (eps : Fin 3 → Fin M → Bool) (e : Fin 3 → Fin M → ℕ)
    (he : ∀ r j, 0 < e r j ∧ e r j ∣ q) :
    ∃ y : Fin 3 → Fin M → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin 3 → Fin M → SL(3,F), (∀ r j, c r j ∈ upperUnipotent) ∧
        orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M => (c r j)⁻¹ *
          (((diagonalFieldGraphAut (a r j) (phi r j) (eps r j)*MulAut.conj (y r j)⁻¹)^(q/e r j))
            (c r j)))) = target := by
  classical
  obtain ⟨l0,hl0,y0,hy0,hcover0⟩ := actual_mixed_graph_root01_product hq hM hF
    (a 0) (phi 0) (eps 0) (e 0) (he 0)
  obtain ⟨l1,hl1,y1,hy1,hcover1⟩ := actual_mixed_graph_root12_product hq hM hF
    (a 1) (phi 1) (eps 1) (e 1) (he 1)
  obtain ⟨y2,hcover2⟩ := actual_mixed_graph_central_product hq hM hF
    (a 2) (phi 2) (eps 2) (e 2) (he 2)
  let beta := fun r j => diagonalFieldGraphAut (a r j) (phi r j) (eps r j)
  let g0 := fun j => (beta 0 j*MulAut.conj (y0 j)⁻¹)^(q/e 0 j)
  let g1 := fun j => (beta 1 j*MulAut.conj (y1 j)⁻¹)^(q/e 1 j)
  have hpres0 : ∀ j g, g ∈ upperUnipotent → g0 j g ∈ upperUnipotent := by
    intro j
    apply power_preserves_U
    intro g hg
    rw [hy0 j,MulAut.mul_apply]
    have hb := beta_preserves_U (a 0 j) (phi 0 j) (eps 0 j) g hg
    cases hs : eps 0 j
    · simpa only [hs,Bool.false_eq_true,ite_false] using diag2n_preserves_U
        (show (0:Fin 3) ≠ 1 by decide) (l0 j) (hl0 j) _ hb
    · simpa only [hs,ite_true] using H_preserves_U (l0 j) (hl0 j) _ hb
  have hpres1 : ∀ j g, g ∈ upperUnipotent → g1 j g ∈ upperUnipotent := by
    intro j
    apply power_preserves_U
    intro g hg
    rw [hy1 j,MulAut.mul_apply]
    have hb := beta_preserves_U (a 1 j) (phi 1 j) (eps 1 j) g hg
    cases hs : eps 1 j
    · simpa only [hs,Bool.false_eq_true,ite_false] using diag2n_preserves_U
        (show (1:Fin 3) ≠ 2 by decide) (l1 j) (hl1 j) _ hb
    · simpa only [hs,ite_true] using mirrored_H_preserves_U (l1 j) (hl1 j) _ hb
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
  refine ⟨y,?_⟩
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
    · simpa [X] using T01_mem (t0 j)
    · simpa [X] using T12_mem (t1 j)
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
    rw [ordered_two]
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
    · exact T02_mem _
  · have hpref : orderedProduct (fun k => (cp k)⁻¹*gamma k (cp k)) =
        orderedProduct (fun j => (cp (block2 0 j))⁻¹*g0 j (cp (block2 0 j))) *
          orderedProduct (fun j => (cp (block2 1 j))⁻¹*g1 j (cp (block2 1 j))) := by
      rw [ordered_two]
      have hg : ∀ i j, gamma (block2 i j) = G i j := by
        intro i j
        dsimp only [gamma,block2]
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
/-- The preceding actual orbital reconstruction in one increasing index tuple.
The three blocks retain their printed order, with the same correction-before-target
quantifiers and the original q/e exponents. -/
theorem actual_A2_graph_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(4*q+1) < M)
    (hF : 4*(4*q+1)^q < Fintype.card F)
    (a : Fin (3*M) → Fin 3 → Fˣ) (phi : Fin (3*M) → RingAut F)
    (eps : Fin (3*M) → Bool) (e : Fin (3*M) → ℕ)
    (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin (3*M) → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin (3*M) → SL(3,F), (∀ j, c j ∈ upperUnipotent) ∧
        orderedProduct (fun j => (c j)⁻¹ *
          (((diagonalFieldGraphAut (a j) (phi j) (eps j)*MulAut.conj (y j)⁻¹)^(q/e j))
            (c j))) = target := by
  classical
  obtain ⟨yb,hyb⟩ := actual_A2_diagonal_field_graph_orbital_product hq hM hF
    (fun r j => a (finProdFinEquiv (r,j))) (fun r j => phi (finProdFinEquiv (r,j)))
    (fun r j => eps (finProdFinEquiv (r,j))) (fun r j => e (finProdFinEquiv (r,j)))
    (fun r j => he _)
  let y := fun j : Fin (3*M) => yb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨y,?_⟩
  intro target ht
  obtain ⟨cb,hmem,hval⟩ := hyb target ht
  let c := fun j : Fin (3*M) => cb (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨c,fun j => hmem _ _,?_⟩
  rw [(a2Kernel% ordered_blocks)]
  change orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M =>
    (c (finProdFinEquiv (r,j)))⁻¹ *
      (((diagonalFieldGraphAut (a (finProdFinEquiv (r,j))) (phi (finProdFinEquiv (r,j)))
        (eps (finProdFinEquiv (r,j)))*MulAut.conj (y (finProdFinEquiv (r,j)))⁻¹)^
          (q/e (finProdFinEquiv (r,j)))) (c (finProdFinEquiv (r,j)))))) = target
  simpa only [c,y,Equiv.symm_apply_apply] using hval
end NikolovSegal.PartIIA2GraphReconstruction
