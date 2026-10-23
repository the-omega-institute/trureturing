/- GID: D5/S3/ConceptDynamics/Coding/ResetSquareIntegralDefect
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetSquareIntegralDefect
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Period-four integral defects of squared reset time and its primitive five-clock. -/
import D5.S1.Recurrence.FiniteCompanionSquareDefect
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
open Multiplicative
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
open D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (VertexModule transition)
open D5.S1.Recurrence

abbrev Row := MonoidAlgebra ℤ Sign
private abbrev tau : Sign := ofAdd true

/-- Literal coefficient coordinates, an integral basis rather than sign eigenvectors. -/
def rowEquiv : Row ≃+ ℤ × ℤ where
  toFun x := (x.coeff 1, x.coeff tau)
  invFun z := MonoidAlgebra.single 1 z.1 + MonoidAlgebra.single tau z.2
  left_inv x := by
    ext h
    rcases sign_cases h with rfl | rfl <;>
      simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, tau]
  right_inv z := by
    apply Prod.ext <;> simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, tau]
  map_add' x y := by rfl

private theorem flip_coordinates (x : Row) :
    rowEquiv (resetFlip x) = ((rowEquiv x).2, (rowEquiv x).1) := by
  apply Prod.ext
  · exact flip_coeff x 1
  · change (resetFlip x).coeff tau = x.coeff 1
    rw [flip_coeff]
    congr 1

/-- Identity plus the square of the original integer right-row transition. -/
def resetSquareDefect (q : ℕ) : Module.End ℤ (VertexModule Sign q) :=
  LinearMap.id + transition (resetMatrix q) ^ 2

theorem time_eq (n : ℕ) :
    (transition (resetMatrix (n + 1))).toAddMonoidHom = FiniteCompanionSquareDefect.time resetFlip n := by
  apply AddMonoidHom.ext
  intro v
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change transition (resetMatrix (n + 1)) v 0 = resetFlip (∑ i, v i)
    exact transition_zero n v
  · exact transition_succ n v j

private theorem defect_eq (n : ℕ) (v : VertexModule Sign (n + 1)) :
    resetSquareDefect (n + 1) v = FiniteCompanionSquareDefect.squareDefect resetFlip n v := by
  change v + transition (resetMatrix (n + 1)) (transition (resetMatrix (n + 1)) v) = _
  have h (v : VertexModule Sign (n + 1)) :
      transition (resetMatrix (n + 1)) v = FiniteCompanionSquareDefect.time resetFlip n v :=
    congrArg (fun f : VertexModule Sign (n + 1) →+ VertexModule Sign (n + 1) => f v) (time_eq n)
  rw [h, h]; rfl

private theorem normal (n : ℕ) (v : VertexModule Sign (n + 2)) :
    FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n (resetSquareDefect (n + 2) v) =
      (FiniteCompanionSquareDefect.headNormal resetFlip (n + 2) (FiniteCompanionSquareDefect.normalDomainEquiv resetFlip n v).1,
        (FiniteCompanionSquareDefect.normalDomainEquiv resetFlip n v).2) := by
  rw [defect_eq]
  exact FiniteCompanionSquareDefect.normal_form resetFlip flip_twice n v

def fiveBlock : Row →+ Row :=
  AddMonoidHom.id Row + AddMonoidHom.id Row + AddMonoidHom.id Row + resetFlip + resetFlip

private theorem five_coeff (x : Row) :
    rowEquiv (fiveBlock x) =
      (3 * (rowEquiv x).1 + 2 * (rowEquiv x).2,
        2 * (rowEquiv x).1 + 3 * (rowEquiv x).2) := by
  change rowEquiv (x+x+x+resetFlip x+resetFlip x) = _
  simp only [map_add, flip_coordinates, Prod.fst_add, Prod.snd_add]
  apply Prod.ext <;> dsimp <;> ring

/-- The integral five-block is injective and has exactly the primitive sum obstruction.
If r+s=5k, its preimage has coefficients r-2k and s-2k. -/
theorem five_block_classification (x y : Row) :
    (fiveBlock x = 0 ↔ x = 0) ∧
      ((∃ a : Row, fiveBlock a = y) ↔ (5 : ℤ) ∣ y.coeff 1 + y.coeff tau) := by
  constructor
  · constructor
    · intro hx
      have hh := congrArg rowEquiv hx
      rw [five_coeff, map_zero] at hh
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      apply rowEquiv.injective
      apply Prod.ext <;> simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
      · dsimp at h1 h2 ⊢; omega
      · dsimp at h1 h2 ⊢; omega
    · rintro rfl; exact map_zero _
  · constructor
    · rintro ⟨a, rfl⟩
      have hh := five_coeff a
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      change (5 : ℤ) ∣ (rowEquiv (fiveBlock a)).1 + (rowEquiv (fiveBlock a)).2
      rw [h1,h2]
      exact ⟨(rowEquiv a).1 + (rowEquiv a).2, by ring⟩
    · rintro ⟨k, hk⟩
      refine ⟨rowEquiv.symm (y.coeff 1 - 2*k, y.coeff tau - 2*k), ?_⟩
      apply rowEquiv.injective
      rw [five_coeff, AddEquiv.apply_symm_apply]
      apply Prod.ext <;> change _ = _
      · change 3*(y.coeff 1-2*k)+2*(y.coeff tau-2*k) = y.coeff 1
        omega
      · change 2*(y.coeff 1-2*k)+3*(y.coeff tau-2*k) = y.coeff tau
        omega

private def rowDouble : Row →+ Row := AddMonoidHom.id Row + AddMonoidHom.id Row
private def rowPlus : Row →+ Row := AddMonoidHom.id Row + resetFlip

private def rowResidue (m : ℕ) : Row →+ ZMod m × ZMod m where
  toFun x := ((x.coeff 1 : ZMod m), (x.coeff tau : ZMod m))
  map_zero' := by simp
  map_add' x y := by simp [MonoidAlgebra.coeff_add]

private def rowFive : Row →+ ZMod 5 where
  toFun x := ((x.coeff 1 + x.coeff tau : ℤ) : ZMod 5)
  map_zero' := by simp
  map_add' x y := by simp [MonoidAlgebra.coeff_add]; ring

private def rowDifference : Row →+ ℤ where
  toFun x := x.coeff 1 - x.coeff tau
  map_zero' := by simp
  map_add' x y := by simp [MonoidAlgebra.coeff_add]; ring

private theorem double_kernel (x : Row) : rowDouble x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply rowEquiv.injective
    have h := congrArg rowEquiv hx
    change rowEquiv (x+x) = 0 at h
    rw [map_add] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext <;> simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    · dsimp at h1 ⊢; omega
    · dsimp at h2 ⊢; omega
  · rintro rfl; exact map_zero _

private theorem double_image (y : Row) :
    (∃ x, rowDouble x = y) ↔ rowResidue 2 y = 0 := by
  change (∃ x, x+x = y) ↔ _
  constructor
  · rintro ⟨x,rfl⟩
    apply Prod.ext
    all_goals simp only [rowResidue, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      MonoidAlgebra.coeff_add, Finsupp.add_apply, Int.cast_add, Prod.fst_zero, Prod.snd_zero]
    all_goals change (_ : ZMod 2) + _ = 0
    all_goals have h2 : (2 : ZMod 2) = 0 := by decide
    all_goals rw [← two_mul, h2, zero_mul]
  · intro hy
    have h1 : (y.coeff 1 : ZMod 2) = 0 := congrArg Prod.fst hy
    have h2 : (y.coeff tau : ZMod 2) = 0 := congrArg Prod.snd hy
    obtain ⟨r,hr⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h1
    obtain ⟨s,hs⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
    refine ⟨rowEquiv.symm (r,s), rowEquiv.injective ?_⟩
    rw [map_add, AddEquiv.apply_symm_apply]
    apply Prod.ext
    · change r+r = y.coeff 1; omega
    · change s+s = y.coeff tau; omega

private theorem plus_image (y : Row) :
    (∃ x, rowPlus x = y) ↔ rowDifference y = 0 := by
  have h := reset_odd_image 1 (by decide) (by decide) (fun _ => y)
  have hc (x : VertexModule Sign 1) : resetDefect 1 x = (fun _ => rowPlus (x 0)) := by
    rw [reset_defect_companion 0]
    ext i; fin_cases i
    simp [D5.S1.Recurrence.FiniteCompanionDefect.companion, rowPlus]
  have hh : (∃ x : VertexModule Sign 1, resetDefect 1 x = (fun _ => y)) ↔
      (∃ x : Row, rowPlus x = y) := by
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨x 0, by simpa only [hc] using congrFun hx 0⟩
    · rintro ⟨x,hx⟩
      exact ⟨fun _ => x, by rw [hc]; exact funext (fun _ => hx)⟩
  rw [hh] at h
  simpa [resetCharacter, rowDifference] using h

private def antiRow : Row := resetOddVector 1 0

private theorem plus_kernel (x : Row) :
    rowPlus x = 0 ↔ ∃! k : ℤ, x = k • antiRow := by
  have h := reset_odd_kernel 1 (by decide) (by decide) (fun _ => x)
  have hc : resetDefect 1 (fun _ => x) = (fun _ => rowPlus x) := by
    rw [reset_defect_companion 0]
    ext i; fin_cases i
    simp [D5.S1.Recurrence.FiniteCompanionDefect.companion, rowPlus]
  rw [hc] at h
  have hl : ((fun _ : Fin 1 => rowPlus x) = 0) ↔ rowPlus x = 0 := by
    constructor
    · intro hh; exact congrFun hh 0
    · intro hh; exact funext (fun _ => hh)
  rw [hl] at h
  rw [h]
  apply existsUnique_congr
  intro k
  constructor
  · intro hk; exact congrFun hk 0
  · intro hk
    funext i; fin_cases i; exact hk

/-- The ordinary two-head cokernel types in the four residue classes. -/
def Obstruction (r : ℕ) : Type :=
  match r with
  | 0 => Fin 0 → ℤ
  | 1 => ZMod 2 × ZMod 2
  | 2 => ZMod 5
  | _+3 => ℤ × ℤ

instance (r : ℕ) : AddCommGroup (Obstruction r) :=
  match r with
  | 0 => inferInstanceAs (AddCommGroup (Fin 0 → ℤ))
  | 1 => inferInstanceAs (AddCommGroup (ZMod 2 × ZMod 2))
  | 2 => inferInstanceAs (AddCommGroup (ZMod 5))
  | _+3 => inferInstanceAs (AddCommGroup (ℤ × ℤ))
private def headReadout (r : ℕ) : (Row × Row) →+ Obstruction r :=
  match r with
  | 0 => 0
  | 1 => (rowResidue 2).comp (AddMonoidHom.fst Row Row)
  | 2 => rowFive.comp (AddMonoidHom.fst Row Row)
  | _+3 => rowDifference.prodMap rowDifference

private theorem head_image (q : ℕ) (z : Row × Row) :
    (∃ a, FiniteCompanionSquareDefect.headNormal resetFlip q a = z) ↔ headReadout (q % 4) z = 0 := by
  have hm := Nat.mod_lt q (by decide : 0 < 4)
  interval_cases h : q % 4
  · simp [FiniteCompanionSquareDefect.headNormal, headReadout, h, Obstruction]
    rfl
  · change (∃ a, FiniteCompanionSquareDefect.headNormal resetFlip q a = z) ↔ _
    simp only [FiniteCompanionSquareDefect.headNormal, h, Nat.zero_ne_one, Nat.reduceEqDiff,
      if_false, if_true]
    have he : (∃ a : Row × Row, (a.1+a.1,a.2) = z) ↔ ∃ x, rowDouble x = z.1 := by
      constructor
      · rintro ⟨a,ha⟩; exact ⟨a.1, congrArg Prod.fst ha⟩
      · rintro ⟨x,hx⟩; exact ⟨(x,z.2), Prod.ext hx rfl⟩
    rw [he, double_image]
    rfl
  · have he : (∃ a : Row × Row, FiniteCompanionSquareDefect.headNormal resetFlip q a = z) ↔
        ∃ x, fiveBlock x = z.1 := by
      simp only [FiniteCompanionSquareDefect.headNormal, h, Nat.reduceEqDiff, if_false, if_true]
      constructor
      · rintro ⟨a,ha⟩; exact ⟨a.1, congrArg Prod.fst ha⟩
      · rintro ⟨x,hx⟩; exact ⟨(x,z.2), Prod.ext hx rfl⟩
    rw [he, (five_block_classification 0 z.1).2]
    change _ ↔ rowFive z.1 = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).symm
  · have he : (∃ a : Row × Row, FiniteCompanionSquareDefect.headNormal resetFlip q a = z) ↔
        (∃ x, rowPlus x = z.1) ∧ (∃ y, rowPlus y = z.2) := by
      simp only [FiniteCompanionSquareDefect.headNormal, h, Nat.reduceEqDiff, if_false]
      constructor
      · rintro ⟨a,ha⟩; exact ⟨⟨a.1, congrArg Prod.fst ha⟩,⟨a.2, congrArg Prod.snd ha⟩⟩
      · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩; exact ⟨(x,y),Prod.ext hx hy⟩
    rw [he, plus_image, plus_image]
    change _ ↔ (rowDifference z.1,rowDifference z.2) = (0,0)
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

private theorem head_readout_surjective (r : ℕ) : Function.Surjective (headReadout r) := by
  rcases r with _ | _ | _ | r
  · intro y
    refine ⟨0, ?_⟩
    change (0 : Fin 0 → ℤ) = y
    funext i; exact Fin.elim0 i
  · rintro ⟨a,b⟩
    obtain ⟨x,hx⟩ := ZMod.intCast_surjective a
    obtain ⟨y,hy⟩ := ZMod.intCast_surjective b
    refine ⟨(rowEquiv.symm (x,y),0), ?_⟩
    change rowResidue 2 (rowEquiv.symm (x,y)) = (a,b)
    have hh := rowEquiv.apply_symm_apply (x,y)
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    change (((rowEquiv (rowEquiv.symm (x,y))).1 : ZMod 2),
      ((rowEquiv (rowEquiv.symm (x,y))).2 : ZMod 2)) = (a,b)
    rw [h1,h2,hx,hy]
  · intro a
    change ZMod 5 at a
    obtain ⟨x,hx⟩ := ZMod.intCast_surjective a
    refine ⟨(MonoidAlgebra.single 1 x,0), ?_⟩
    change rowFive (MonoidAlgebra.single 1 x) = a
    simpa [headReadout, rowFive, MonoidAlgebra.coeff_single, tau] using hx
  · rintro ⟨a,b⟩
    refine ⟨(MonoidAlgebra.single 1 a,MonoidAlgebra.single 1 b), ?_⟩
    change (rowDifference (MonoidAlgebra.single 1 a),
      rowDifference (MonoidAlgebra.single 1 b)) = (a,b)
    simp [rowDifference, MonoidAlgebra.coeff_single, tau]

/-- A primitive readout of the ordinary image quotient; it uses the codomain change. -/
def resetSquareReadout (q : ℕ) : VertexModule Sign q →ₗ[ℤ] Obstruction (q % 4) :=
  (match q with
  | 0 => 0
  | 1 => (rowResidue 2).comp
      ({toFun := fun v => v 0, map_zero' := rfl, map_add' := fun _ _ => rfl} :
        VertexModule Sign 1 →+ Row)
  | n + 2 => (headReadout ((n + 2)%4)).comp
      ((AddMonoidHom.fst _ _).comp (FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n).toAddMonoidHom)
  : VertexModule Sign q →+ Obstruction (q % 4)).toIntLinearMap

/-- Exact ordinary image criterion at every positive length, including the doubling
map at length one. No kernel is added to this quotient. -/
theorem reset_square_image (q : ℕ) (hq : 0 < q) (y : VertexModule Sign q) :
    (∃ v, resetSquareDefect q v = y) ↔ resetSquareReadout q y = 0 := by
  cases q with
  | zero => omega
  | succ q => cases q with
    | zero =>
      have hd (v : VertexModule Sign 1) : resetSquareDefect 1 v = v+v := by
        rw [defect_eq 0]
        ext i; fin_cases i
        simp [FiniteCompanionSquareDefect.squareDefect, FiniteCompanionSquareDefect.time, flip_twice]
      have he : (∃ v : VertexModule Sign 1, resetSquareDefect 1 v = y) ↔
          ∃ x : Row, rowDouble x = y 0 := by
        constructor
        · rintro ⟨v,hv⟩; exact ⟨v 0, by change v 0 + v 0 = y 0; simpa only [hd,Pi.add_apply] using congrFun hv 0⟩
        · rintro ⟨x,hx⟩
          refine ⟨fun _ => x, ?_⟩
          rw [hd]; funext i; fin_cases i; exact hx
      rw [he, double_image]
      rfl
    | succ n =>
      let C := FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n
      let D := FiniteCompanionSquareDefect.normalDomainEquiv resetFlip n
      have he : (∃ v, resetSquareDefect (n + 2) v = y) ↔
          ∃ a, FiniteCompanionSquareDefect.headNormal resetFlip (n + 2) a = (C y).1 := by
        constructor
        · rintro ⟨v,rfl⟩; exact ⟨(D v).1, (congrArg Prod.fst (normal n v)).symm⟩
        · rintro ⟨a,ha⟩
          refine ⟨D.symm (a,(C y).2), C.injective ?_⟩
          rw [normal]
          change (FiniteCompanionSquareDefect.headNormal resetFlip (n + 2) (D (D.symm (a,(C y).2))).1,
            (D (D.symm (a,(C y).2))).2) = C y
          rw [D.apply_symm_apply, ha]
      rw [he, head_image]
      rfl

/-- The readout is onto its entire residue-dependent arithmetic target. -/
theorem reset_square_readout_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (resetSquareReadout q) := by
  cases q with
  | zero => omega
  | succ q => cases q with
    | zero =>
      intro y
      obtain ⟨z,hz⟩ := head_readout_surjective 1 y
      exact ⟨fun _ => z.1,hz⟩
    | succ n =>
      intro y
      obtain ⟨z,hz⟩ := head_readout_surjective ((n + 2)%4) y
      refine ⟨(FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n).symm (z,0), ?_⟩
      change headReadout ((n + 2)%4)
        ((FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n)
          ((FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n).symm (z,0))).1 = y
      rw [AddEquiv.apply_symm_apply]; exact hz

/-- The ordinary cokernel is respectively zero, (ZMod 2)^2, ZMod 5, or Z^2. -/
def resetSquareCokernelEquiv (q : ℕ) (hq : 0 < q) :
    (VertexModule Sign q ⧸ LinearMap.range (resetSquareDefect q)) ≃ₗ[ℤ] Obstruction (q % 4) :=
  (Submodule.quotEquivOfEq _ _ (by ext y; exact reset_square_image q hq y)).trans
    ((resetSquareReadout q).quotKerEquivOfSurjective (reset_square_readout_surjective q hq))

private theorem head_kernel (q : ℕ) (z : Row × Row) :
    FiniteCompanionSquareDefect.headNormal resetFlip q z = 0 ↔
      if q % 4 = 3 then ∃! k : ℤ × ℤ, z = (k.1 • antiRow,k.2 • antiRow) else z = 0 := by
  have hm := Nat.mod_lt q (by decide : 0 < 4)
  interval_cases h : q % 4
  · simp [FiniteCompanionSquareDefect.headNormal,h]
  · simp only [FiniteCompanionSquareDefect.headNormal,h,Nat.reduceEqDiff,if_false,if_true]
    change (rowDouble z.1,z.2) = 0 ↔ z = 0
    change (rowDouble z.1,z.2) = (0,0) ↔ z = (0,0)
    simp only [Prod.mk.injEq, double_kernel]
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩
  · simp only [FiniteCompanionSquareDefect.headNormal,h,Nat.reduceEqDiff,if_false,if_true]
    change (fiveBlock z.1,z.2) = 0 ↔ z = 0
    change (fiveBlock z.1,z.2) = (0,0) ↔ z = (0,0)
    simp only [Prod.mk.injEq, (five_block_classification z.1 0).1]
    exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩
  · simp only [FiniteCompanionSquareDefect.headNormal,h,Nat.reduceEqDiff,if_false,if_true]
    change (rowPlus z.1,rowPlus z.2) = 0 ↔ _
    change (rowPlus z.1,rowPlus z.2) = (0,0) ↔ _
    simp only [Prod.mk.injEq, plus_kernel]
    constructor
    · rintro ⟨⟨a,ha,hua⟩,⟨b,hb,hub⟩⟩
      refine ⟨(a,b),Prod.ext ha hb, ?_⟩
      intro k hk
      exact Prod.ext (hua k.1 (congrArg Prod.fst hk)) (hub k.2 (congrArg Prod.snd hk))
    · rintro ⟨k,hk,huk⟩
      constructor
      · refine ⟨k.1, congrArg Prod.fst hk, ?_⟩
        intro a ha
        have hb : z.2 = k.2 • antiRow := congrArg Prod.snd hk
        exact congrArg Prod.fst (huk (a,k.2) (Prod.ext ha hb))
      · refine ⟨k.2, congrArg Prod.snd hk, ?_⟩
        intro b hb
        have ha : z.1 = k.1 • antiRow := congrArg Prod.fst hk
        exact congrArg Prod.snd (huk (k.1,b) (Prod.ext ha hb))

/-- The two primitive resonant generators, reconstructed on the original lattice. -/
def resetSquareKernelVector (q : ℕ) (k : ℤ × ℤ) : VertexModule Sign q :=
  match q with
  | 0 => 0
  | 1 => 0
  | n + 2 => (FiniteCompanionSquareDefect.normalDomainEquiv resetFlip n).symm ((k.1 • antiRow,k.2 • antiRow),0)

/-- The full kernel is zero except in residue three, where it has two independent
primitive integer parameters. This statement retains every positive length. -/
theorem reset_square_kernel (q : ℕ) (hq : 0 < q) (v : VertexModule Sign q) :
    resetSquareDefect q v = 0 ↔
      if q % 4 = 3 then ∃! k : ℤ × ℤ, v = resetSquareKernelVector q k else v = 0 := by
  cases q with
  | zero => omega
  | succ q => cases q with
    | zero =>
      change resetSquareDefect 1 v = 0 ↔ v = 0
      have hd : resetSquareDefect 1 v = v+v := by
        rw [defect_eq 0]
        ext i; fin_cases i
        simp [FiniteCompanionSquareDefect.squareDefect, FiniteCompanionSquareDefect.time, flip_twice]
      rw [hd]
      constructor
      · intro hv; funext i; fin_cases i
        exact (double_kernel (v 0)).mp (congrFun hv 0)
      · rintro rfl; simp
    | succ n =>
      let C := FiniteCompanionSquareDefect.normalCodomainEquiv resetFlip n
      let D := FiniteCompanionSquareDefect.normalDomainEquiv resetFlip n
      have he : resetSquareDefect (n + 2) v = 0 ↔
          FiniteCompanionSquareDefect.headNormal resetFlip (n + 2) (D v).1 = 0 ∧ (D v).2 = 0 := by
        rw [← C.injective.eq_iff, map_zero, normal]
        exact Prod.ext_iff
      rw [he, head_kernel]
      by_cases h3 : (n + 2)%4 = 3
      · simp only [h3,if_true]
        constructor
        · rintro ⟨⟨k,hk,huk⟩,ht⟩
          refine ⟨k,D.injective ?_, ?_⟩
          · change D v = D (D.symm ((k.1 • antiRow,k.2 • antiRow),0))
            rw [D.apply_symm_apply]; exact Prod.ext hk ht
          · intro l hl
            apply huk
            have hh := congrArg D hl
            change D v = D (D.symm ((l.1 • antiRow,l.2 • antiRow),0)) at hh
            rw [D.apply_symm_apply] at hh
            exact congrArg Prod.fst hh
        · rintro ⟨k,hk,huk⟩
          have hh := congrArg D hk
          change D v = D (D.symm ((k.1 • antiRow,k.2 • antiRow),0)) at hh
          rw [D.apply_symm_apply] at hh
          refine ⟨⟨k,congrArg Prod.fst hh,?_⟩,congrArg Prod.snd hh⟩
          intro l hl
          apply huk
          apply D.injective
          change D v = D (D.symm ((l.1 • antiRow,l.2 • antiRow),0))
          rw [D.apply_symm_apply]
          have ht : (D v).2 = 0 := congrArg Prod.snd hh
          exact Prod.ext hl ht
      · simp only [h3,if_false]
        constructor
        · rintro ⟨hh,ht⟩
          apply D.injective
          rw [map_zero]
          exact Prod.ext hh ht
        · rintro rfl; simp

private def rowAugmentation : Row →+ ℤ :=
  (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ).comp rowEquiv.toAddMonoidHom

private theorem aug_flip (x : Row) : rowAugmentation (resetFlip x) = rowAugmentation x := by
  change (rowEquiv (resetFlip x)).1 + (rowEquiv (resetFlip x)).2 = _
  rw [flip_coordinates]
  change (rowEquiv x).2 + (rowEquiv x).1 = (rowEquiv x).1 + (rowEquiv x).2
  abel

/-- The primitive five-clock weights in actual vertex order. -/
def clockWeight (i : ℕ) : ZMod 5 :=
  if i % 4 = 0 then 1 else if i % 4 = 1 then 2 else if i % 4 = 2 then 0 else 4

private theorem weight_step (i : ℕ) : clockWeight (i + 1) = 3*clockWeight i - 1 := by
  have hm := Nat.mod_lt i (by decide : 0 < 4)
  have hs : (i + 1)%4 = (i % 4+1)%4 := by omega
  interval_cases h : i % 4 <;> simp only [clockWeight,h,hs] <;> decide

/-- Weighted augmentation with the repeating coefficients 1,2,0,4 modulo five. -/
def resetFiveClock (q : ℕ) : VertexModule Sign q →ₗ[ℤ] ZMod 5 :=
  ({ toFun := fun v => ∑ i : Fin q, clockWeight i.val * (rowAugmentation (v i) : ZMod 5)
     map_zero' := by simp
     map_add' := by intro v w; simp [map_add, mul_add, Finset.sum_add_distrib]
   } : VertexModule Sign q →+ ZMod 5).toIntLinearMap

private theorem clock_apply (q : ℕ) (v : VertexModule Sign q) :
    resetFiveClock q v = ∑ i : Fin q, clockWeight i.val * (rowAugmentation (v i) : ZMod 5) := rfl

/-- Genuine time, in the original right-row orientation, multiplies the primitive
clock by three at every length congruent to two modulo four. -/
theorem reset_five_clock_time (q : ℕ) (h2 : q % 4 = 2) (v : VertexModule Sign q) :
    resetFiveClock q (transition (resetMatrix q) v) = 3 * resetFiveClock q v := by
  cases q with
  | zero => norm_num at h2
  | succ n =>
      have hn : n%4 = 1 := by omega
      have hw : clockWeight n = 2 := by simp [clockWeight,hn]
      change (∑ i : Fin (n + 1), clockWeight i.val *
        (rowAugmentation (transition (resetMatrix (n + 1)) v i) : ZMod 5)) =
        3 * (∑ i : Fin (n + 1), clockWeight i.val * (rowAugmentation (v i) : ZMod 5))
      rw [Fin.sum_univ_succ]
      have hw0 : clockWeight 0 = 1 := rfl
      simp only [Fin.val_zero, Fin.val_succ, hw0,
        one_mul, transition_zero, transition_succ]
      change (rowAugmentation (resetFlip (∑ i, v i)) : ZMod 5) +
        (∑ j : Fin n, clockWeight (j.val+1) * (rowAugmentation (v j.castSucc) : ZMod 5)) = _
      rw [aug_flip, map_sum, Int.cast_sum]
      rw [Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (rowAugmentation (v i) : ZMod 5)),
        Fin.sum_univ_castSucc (fun i : Fin (n + 1) => clockWeight i.val *
          (rowAugmentation (v i) : ZMod 5))]
      simp only [Fin.val_castSucc, Fin.val_last, hw]
      simp_rw [weight_step, sub_mul, one_mul]
      simp_rw [mul_assoc]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have h6 : (3:ZMod 5)*2 = 1 := by decide
      rw [mul_add, ← mul_assoc, h6, one_mul]
      ring

/-- The clock is primitive: every residue is reached from the identity coefficient
at vertex zero. No rational basis change occurs. -/
theorem reset_five_clock_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (resetFiveClock q) := by
  cases q with
  | zero => omega
  | succ n =>
      intro a
      obtain ⟨k,hk⟩ := ZMod.intCast_surjective a
      refine ⟨Fin.cons (MonoidAlgebra.single 1 k) (0 : Fin n → Row), ?_⟩
      have ha : rowAugmentation (MonoidAlgebra.single (1 : Sign) k) = k := by
        change (MonoidAlgebra.single (1 : Sign) k).coeff 1 +
          (MonoidAlgebra.single (1 : Sign) k).coeff tau = k
        simp [MonoidAlgebra.coeff_single,tau]
      rw [clock_apply, Fin.sum_univ_succ]
      change clockWeight 0 * (rowAugmentation (MonoidAlgebra.single 1 k) : ZMod 5) +
        (∑ j : Fin n, clockWeight j.succ.val * (rowAugmentation (0 : Row) : ZMod 5)) = a
      rw [ha, map_zero]
      simp only [Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero,
        show clockWeight 0 = 1 from rfl, one_mul]
      exact hk

private theorem clock_defect (q : ℕ) (h2 : q % 4 = 2) (v : VertexModule Sign q) :
    resetFiveClock q (resetSquareDefect q v) = 0 := by
  change resetFiveClock q (v + transition (resetMatrix q) (transition (resetMatrix q) v)) = 0
  rw [map_add, reset_five_clock_time q h2, reset_five_clock_time q h2]
  have ht : (10 : ZMod 5) = 0 := by decide
  calc
    _ = 10 * resetFiveClock q v := by ring
    _ = 0 := by rw [ht,zero_mul]

/-- Exact clock-kernel equality. Surjectivity and the independently computed cyclic
five cokernel certify the reverse inclusion, not merely annihilation of the image. -/
theorem reset_five_clock_image (q : ℕ) (h2 : q % 4 = 2) :
    LinearMap.range (resetSquareDefect q) = LinearMap.ker (resetFiveClock q) := by
  have hq : 0 < q := by omega
  let L := resetSquareDefect q
  let f := resetFiveClock q
  have hle : LinearMap.range L ≤ LinearMap.ker f := by
    rintro _ ⟨v,rfl⟩
    exact clock_defect q h2 v
  let fb := (LinearMap.range L).liftQ f hle
  let e : (VertexModule Sign q ⧸ LinearMap.range L) ≃ₗ[ℤ] ZMod 5 := by
    have ee := resetSquareCokernelEquiv q hq
    rw [h2] at ee
    exact ee
  have hs : Function.Surjective fb := by
    intro a
    obtain ⟨v,hv⟩ := reset_five_clock_surjective q hq a
    exact ⟨Submodule.Quotient.mk v,hv⟩
  have hi : Function.Injective (fb.comp e.symm.toLinearMap) :=
    (Finite.injective_iff_surjective).mpr (hs.comp e.symm.surjective)
  have hfi : Function.Injective fb := by
    intro a b hab
    apply e.injective
    apply hi
    simpa using hab
  ext v
  change v ∈ LinearMap.range L ↔ f v = 0
  rw [← Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hv
    have h := congrArg fb hv
    change f v = fb 0 at h
    rw [map_zero] at h
    exact h
  · intro hv
    apply hfi
    change f v = fb 0
    rw [map_zero]
    exact hv

end D5.S3.ConceptDynamics.Coding.ResetSquareIntegralDefect
