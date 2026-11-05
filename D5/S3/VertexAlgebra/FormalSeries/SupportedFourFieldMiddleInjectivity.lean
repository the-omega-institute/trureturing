/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal middle cancellation on genuinely nested four-field support. -/
import D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddlePolynomial
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedPolynomial
import Batteries.Tactic.OpenPrivate

/-! The three new outer factors are cancelled on fixed spectator slices by
accepted three-field kernels. No common cone or uniform third cutoff is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.SupportedFourFieldMiddleInjectivity
open UniformGradedLocalCorrelator SupportedFinalRInjectivity
open ThreeFieldBalancedPolynomial FourFieldMiddlePolynomial
noncomputable section
open private triple_difference_zero yz_difference_zero from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerPolynomial
open private variable_xyz from
  D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Coefficient order is x,b,z,y; the cutoffs are nested in b,y,z. -/
def MiddleSupport (F : Distribution 4 R) : Prop :=
  (∃ B : ℕ, ∀ x b z y : ℤ, b < -(B : ℤ) → F ![x,b,z,y] = 0) ∧
  (∀ b : ℤ, ∃ Y : ℕ, ∀ x z y : ℤ, y < -(Y : ℤ) → F ![x,b,z,y] = 0) ∧
  (∀ b y : ℤ, ∃ Z : ℕ, ∀ x z : ℤ, z < -(Z : ℤ) → F ![x,b,z,y] = 0)

private theorem variable_action (F : Distribution 4 R) (i : Fin 4) (e : Exponent 4) :
    polynomialAction (variablePolynomial i) F e = F (e - Pi.single i 1) := by
  rw [variablePolynomial, polynomialAction, AddMonoidAlgebra.lift_single]
  exact one_smul ℂ _

private theorem variable_xyzy (F : Distribution 4 R) (i : Fin 4) (x b z y : ℤ) :
    polynomialAction (variablePolynomial i) F ![x,b,z,y] =
      F ![x-(if i=0 then 1 else 0), b-(if i=1 then 1 else 0),
        z-(if i=2 then 1 else 0), y-(if i=3 then 1 else 0)] := by
  rw [variable_action]
  congr 1
  funext c
  fin_cases i <;> fin_cases c <;> simp

omit [Algebra ℂ R] in
private theorem support_sub (F G : Distribution 4 R)
    (hF : MiddleSupport F) (hG : MiddleSupport G) : MiddleSupport (F-G) := by
  obtain ⟨⟨B,hb⟩,hy,hz⟩ := hF
  obtain ⟨⟨C,hc⟩,hv,hw⟩ := hG
  refine ⟨⟨max B C, ?_⟩, ?_, ?_⟩
  · intro x b z y h
    change F _ - G _ = 0
    rw [hb x b z y (by omega),hc x b z y (by omega),sub_self]
  · intro b
    obtain ⟨Y,hY⟩ := hy b
    obtain ⟨V,hV⟩ := hv b
    refine ⟨max Y V, ?_⟩
    intro x z y h
    change F _ - G _ = 0
    rw [hY x z y (by omega),hV x z y (by omega),sub_self]
  · intro b y
    obtain ⟨Z,hZ⟩ := hz b y
    obtain ⟨W,hW⟩ := hw b y
    refine ⟨max Z W, ?_⟩
    intro x z h
    change F _ - G _ = 0
    rw [hZ x z (by omega),hW x z (by omega),sub_self]

omit [Algebra ℂ R] in
private theorem support_add (F G : Distribution 4 R)
    (hF : MiddleSupport F) (hG : MiddleSupport G) : MiddleSupport (F+G) := by
  obtain ⟨⟨B,hb⟩,hy,hz⟩ := hF
  obtain ⟨⟨C,hc⟩,hv,hw⟩ := hG
  refine ⟨⟨max B C, ?_⟩, ?_, ?_⟩
  · intro x b z y h
    change F _ + G _ = 0
    rw [hb x b z y (by omega),hc x b z y (by omega),add_zero]
  · intro b
    obtain ⟨Y,hY⟩ := hy b
    obtain ⟨V,hV⟩ := hv b
    refine ⟨max Y V, ?_⟩
    intro x z y h
    change F _ + G _ = 0
    rw [hY x z y (by omega),hV x z y (by omega),add_zero]
  · intro b y
    obtain ⟨Z,hZ⟩ := hz b y
    obtain ⟨W,hW⟩ := hw b y
    refine ⟨max Z W, ?_⟩
    intro x z h
    change F _ + G _ = 0
    rw [hZ x z (by omega),hW x z (by omega),add_zero]

private theorem support_smul (c : ℂ) (F : Distribution 4 R) (hF : MiddleSupport F) :
    MiddleSupport (c • F) := by
  obtain ⟨⟨B,hb⟩,hy,hz⟩ := hF
  refine ⟨⟨B, ?_⟩, ?_, ?_⟩
  · intro x b z y h
    change c • F _ = 0
    rw [hb x b z y h,smul_zero]
  · intro b
    obtain ⟨Y,hY⟩ := hy b
    refine ⟨Y, ?_⟩
    intro x z y h
    change c • F _ = 0
    rw [hY x z y h,smul_zero]
  · intro b y
    obtain ⟨Z,hZ⟩ := hz b y
    refine ⟨Z, ?_⟩
    intro x z h
    change c • F _ = 0
    rw [hZ x z h,smul_zero]

omit [Algebra ℂ R] in
private theorem support_translate (d : Exponent 4) (F : Distribution 4 R)
    (hF : MiddleSupport F) : MiddleSupport (fun e => F (e-d)) := by
  obtain ⟨⟨B,hb⟩,hy,hz⟩ := hF
  have eq (x b z y : ℤ) : (![x,b,z,y] : Exponent 4)-d =
      ![x-d 0,b-d 1,z-d 2,y-d 3] := by
    funext i
    fin_cases i <;> rfl
  refine ⟨⟨B+(-d 1).toNat, ?_⟩, ?_, ?_⟩
  · intro x b z y h
    change F ((![x,b,z,y] : Exponent 4)-d)=0
    rw [eq]
    apply hb
    have := Int.self_le_toNat (-d 1)
    omega
  · intro b
    obtain ⟨Y,hY⟩ := hy (b-d 1)
    refine ⟨Y+(-d 3).toNat, ?_⟩
    intro x z y h
    change F ((![x,b,z,y] : Exponent 4)-d)=0
    rw [eq]
    apply hY
    have := Int.self_le_toNat (-d 3)
    omega
  · intro b y
    obtain ⟨Z,hZ⟩ := hz (b-d 1) (y-d 3)
    refine ⟨Z+(-d 2).toNat, ?_⟩
    intro x z h
    change F ((![x,b,z,y] : Exponent 4)-d)=0
    rw [eq]
    apply hZ
    have := Int.self_le_toNat (-d 2)
    omega

private theorem support_action (p : LaurentPolynomial 4) (F : Distribution 4 R)
    (hF : MiddleSupport F) : MiddleSupport (polynomialAction p F) := by
  induction p using AddMonoidAlgebra.induction_on with
  | of d =>
    change MiddleSupport (polynomialAction (AddMonoidAlgebra.single d 1) F)
    have h := support_translate d F hF
    rw [polynomialAction,AddMonoidAlgebra.lift_single]
    change MiddleSupport (fun e => (1 : ℂ) • F (e-d))
    simpa only [one_smul] using h
  | add p q hp hq =>
    simpa only [map_add,LinearMap.add_apply] using support_add _ _ hp hq
  | smul c p hp =>
    simpa only [map_smul,LinearMap.smul_apply] using support_smul c _ hp

private theorem power_zero (p : LaurentPolynomial 4)
    (kill : ∀ F : Distribution 4 R, MiddleSupport F → polynomialAction p F=0 → F=0)
    (n : ℕ) (F : Distribution 4 R) (hF : MiddleSupport F)
    (hz : polynomialAction (p^n) F=0) : F=0 := by
  induction n generalizing F with
  | zero => simpa using hz
  | succ n ih =>
    rw [pow_succ',map_mul,Module.End.mul_apply] at hz
    exact ih F hF (kill _ (support_action _ F hF) hz)

private theorem variable_zero (i : Fin 4) (F : Distribution 4 R)
    (hz : polynomialAction (variablePolynomial i) F=0) : F=0 := by
  funext e
  have h := congrFun hz (e+Pi.single i 1)
  rw [variable_action,add_sub_cancel_right] at h
  exact h

private theorem outer_triple_zero (F : Distribution 4 R) (hF : MiddleSupport F)
    (hz : polynomialAction
      (variablePolynomial 0-variablePolynomial 1-variablePolynomial 2) F=0) : F=0 := by
  have rows (y : ℤ) : (fun e : Exponent 3 => F ![e 2,e 0,e 1,y])=0 := by
    apply triple_difference_zero
    · constructor
      · obtain ⟨B,hB⟩ := hF.1
        exact ⟨B,fun b z x h => hB x b z y h⟩
      · intro b
        obtain ⟨Z,hZ⟩ := hF.2.2 b y
        exact ⟨Z,fun z x h => hZ x z h⟩
    · funext e
      have h := congrFun hz ![e 2,e 0,e 1,y]
      have ee : (![e 0,e 1,e 2] : Exponent 3)=e := by
        funext i
        fin_cases i <;> rfl
      rw [← ee]
      simpa [map_sub,LinearMap.sub_apply,Pi.sub_apply,variable_xyz,
        variable_xyzy,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.isValue,reduceIte,
        sub_zero] using h
  funext e
  have h := congrFun (rows (e 3)) ![e 1,e 2,e 0]
  have ee : (![e 0,e 1,e 2,e 3] : Exponent 4)=e := by
    funext i
    fin_cases i <;> rfl
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,ee,Pi.zero_apply] using h

private theorem outer_difference_zero (i : Fin 4) (hi : i=2 ∨ i=3)
    (F : Distribution 4 R) (hF : MiddleSupport F)
    (hz : polynomialAction (variablePolynomial 0-variablePolynomial i) F=0) : F=0 := by
  rcases hi with rfl | rfl
  · have rows (y : ℤ) : (fun e : Exponent 3 => F ![e 2,e 0,e 1,y])=0 := by
      apply yz_difference_zero
      · constructor
        · obtain ⟨B,hB⟩ := hF.1
          exact ⟨B,fun b z x h => hB x b z y h⟩
        · intro b
          obtain ⟨Z,hZ⟩ := hF.2.2 b y
          exact ⟨Z,fun z x h => hZ x z h⟩
      · funext e
        have h := congrFun hz ![e 2,e 0,e 1,y]
        have ee : (![e 0,e 1,e 2] : Exponent 3)=e := by
          funext i
          fin_cases i <;> rfl
        rw [← ee]
        simpa [map_sub,LinearMap.sub_apply,Pi.sub_apply,variable_xyz,
          variable_xyzy,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
          Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.isValue,reduceIte,
          sub_zero] using h
    funext e
    have h := congrFun (rows (e 3)) ![e 1,e 2,e 0]
    have ee : (![e 0,e 1,e 2,e 3] : Exponent 4)=e := by
      funext i
      fin_cases i <;> rfl
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,ee,Pi.zero_apply] using h
  · have rows (z : ℤ) : (fun e : Exponent 3 => F ![e 2,e 0,z,e 1])=0 := by
      apply yz_difference_zero
      · constructor
        · obtain ⟨B,hB⟩ := hF.1
          exact ⟨B,fun b y x h => hB x b z y h⟩
        · intro b
          obtain ⟨Y,hY⟩ := hF.2.1 b
          exact ⟨Y,fun y x h => hY x z y h⟩
      · funext e
        have h := congrFun hz ![e 2,e 0,z,e 1]
        have ee : (![e 0,e 1,e 2] : Exponent 3)=e := by
          funext i
          fin_cases i <;> rfl
        rw [← ee]
        simpa [map_sub,LinearMap.sub_apply,Pi.sub_apply,variable_xyz,
          variable_xyzy,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
          Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.isValue,reduceIte,
          sub_zero] using h
    funext e
    have h := congrFun (rows (e 2)) ![e 1,e 3,e 0]
    have ee : (![e 0,e 1,e 2,e 3] : Exponent 4)=e := by
      funext i
      fin_cases i <;> rfl
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,ee,Pi.zero_apply] using h

private def coreExponent : Exponent 3 →+ Exponent 4 where
  toFun e := ![0,e 0,e 1,e 2]
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' e d := by funext i; fin_cases i <;> rfl

private def corePolynomial : LaurentPolynomial 3 →ₐ[ℂ] LaurentPolynomial 4 :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ coreExponent

private theorem core_action (p : LaurentPolynomial 3) (F : Distribution 4 R) (x : ℤ) :
    polynomialAction p (fun e => F ![x,e 0,e 1,e 2]) =
      fun e => polynomialAction (corePolynomial p) F ![x,e 0,e 1,e 2] := by
  induction p using AddMonoidAlgebra.induction_on with
  | of d =>
    change polynomialAction (AddMonoidAlgebra.single d 1) (fun e => F ![x,e 0,e 1,e 2]) =
      fun e => polynomialAction (corePolynomial (AddMonoidAlgebra.single d 1)) F ![x,e 0,e 1,e 2]
    simp only [corePolynomial,AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single,polynomialAction,AddMonoidAlgebra.lift_single]
    funext e
    change (1 : ℂ) • F ![x,(e-d) 0,(e-d) 1,(e-d) 2] =
      (1 : ℂ) • F ((![x,e 0,e 1,e 2] : Exponent 4)-coreExponent d)
    congr 2
    funext i
    fin_cases i <;> simp [coreExponent]
  | add p q hp hq =>
    simp only [map_add,LinearMap.add_apply,hp,hq]
    rfl
  | smul c p hp =>
    simp only [map_smul,LinearMap.smul_apply,hp]
    rfl

private theorem core_variable (i : Fin 3) :
    corePolynomial (variablePolynomial i) = variablePolynomial i.succ := by
  simp only [corePolynomial,variablePolynomial,AddMonoidAlgebra.mapDomainAlgHom_apply,
    AddMonoidAlgebra.mapDomain_single]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> simp [coreExponent]

private theorem middle_zero (k : ℕ) (a : Fin 4 → ℕ) (F : Distribution 4 R)
    (hF : MiddleSupport F) (hz : polynomialAction (middlePolynomial k a) F=0) : F=0 := by
  let C := corePolynomial (balancedPolynomial k (fun i => a i.succ))
  let X : LaurentPolynomial 4 := variablePolynomial 0
  let A : LaurentPolynomial 4 := X-variablePolynomial 1-variablePolynomial 2
  let B : LaurentPolynomial 4 := X-variablePolynomial 2
  let Y : LaurentPolynomial 4 := X-variablePolynomial 3
  have factor : middlePolynomial k a = X^a 0 * A^k * B^k * Y^k * C := by
    dsimp only [C,X,A,B,Y,middlePolynomial,balancedPolynomial]
    simp only [map_mul,map_pow,map_add,map_sub,core_variable]
    simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,show (2 : Fin 3).succ=(3 : Fin 4) from rfl]
    ring
  let FC := polynomialAction C F
  let FY := polynomialAction (Y^k) FC
  let FB := polynomialAction (B^k) FY
  let FA := polynomialAction (A^k) FB
  have sc : MiddleSupport FC := support_action C F hF
  have sy : MiddleSupport FY := support_action _ FC sc
  have sb : MiddleSupport FB := support_action _ FY sy
  have sa : MiddleSupport FA := support_action _ FB sb
  rw [factor,map_mul,map_mul,map_mul,map_mul] at hz
  have ha : FA=0 := power_zero X (fun G _ h => variable_zero 0 G h) (a 0) FA sa hz
  have hb : FB=0 := power_zero A outer_triple_zero k FB sb ha
  have hy : FY=0 := power_zero B (outer_difference_zero 2 (Or.inl rfl)) k FY sy hb
  have hc : FC=0 := power_zero Y (outer_difference_zero 3 (Or.inr rfl)) k FC sc hy
  have rows (x : ℤ) : (fun e : Exponent 3 => F ![x,e 0,e 1,e 2])=0 := by
    apply balanced_injective k (fun i => a i.succ)
    · constructor
      · obtain ⟨U,hU⟩ := hF.1
        exact ⟨U,fun b y z h => hU x b z y h⟩
      · intro b
        obtain ⟨Y,hY⟩ := hF.2.1 b
        exact ⟨Y,fun y z h => hY x z y h⟩
    · exact ⟨⟨0,by intros; rfl⟩,fun _ => ⟨0,by intros; rfl⟩⟩
    · rw [core_action]
      funext e
      simpa only [FC,C,map_zero,Pi.zero_apply] using congrFun hc ![x,e 0,e 1,e 2]
  funext e
  have h := congrFun (rows (e 0)) ![e 1,e 2,e 3]
  have ee : (![e 0,e 1,e 2,e 3] : Exponent 4)=e := by
    funext i
    fin_cases i <;> rfl
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,ee,Pi.zero_apply] using h

/-- Injectivity on the real b,y,z nested support, allowing arbitrary cutoffs. -/
theorem middle_injective (k : ℕ) (a : Fin 4 → ℕ) (F G : Distribution 4 R)
    (hF : MiddleSupport F) (hG : MiddleSupport G)
    (same : polynomialAction (middlePolynomial k a) F =
      polynomialAction (middlePolynomial k a) G) : F=G := by
  apply sub_eq_zero.mp
  apply middle_zero k a _ (support_sub F G hF hG)
  rw [map_sub,same,sub_self]

end
end D5.S3.VertexAlgebra.SupportedFourFieldMiddleInjectivity
