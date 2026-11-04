/- GID: D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/FourFieldMiddleNativeInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native middle inversion on signed homogeneous numerator slices. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedFourFieldMiddleInjectivity
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedInverseCoefficients
import Batteries.Tactic.OpenPrivate

/-! Native coefficients use b=STU, y=TU, z=U and the fourth, total,
degree. Only the numerator is read into native power series. Finite raw
translations prove the actual action; no substitution of a raw distribution
or support-cone premise is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FourFieldMiddleNativeInverse
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open SupportedFinalCovariance ThreeFieldBalancedNativeInverse
open ThreeFieldFinalCone FourFieldMiddlePolynomial SupportedFourFieldMiddleInjectivity
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Total exponent, including the outer coordinate. -/
def total (e : Exponent 4) : ℤ := e 0+e 1+e 2+e 3

def degree (k : ℕ) (a : Fin 4 → ℕ) : ℕ := a 0+a 1+a 2+a 3+6*k

private def W (e : Exponent 4) : Exponent 3 := ![e 1,e 1+e 3,e 1+e 3+e 2]

def middleShift (k : ℕ) (a : Fin 4 → ℕ) : Exponent 3 :=
  ![(k : ℤ),k+a 3,a 1+a 2+a 3+3*k]

/-- A native homogeneous slice of a generally infinite four-variable series.
Signed extension retains the fourth-coordinate negative branch. -/
def numeratorSlice (P : MvPowerSeries (Fin 4) R) (t : ℤ) : MvPowerSeries (Fin 3) R :=
  fun d => if d 0 ≤ d 1 ∧ d 1 ≤ d 2 then
    signedExtend P ![t-d 2,d 0,(d 2 : ℤ)-d 1,(d 1 : ℤ)-d 0] else 0

/-- The three-variable unit; the fourth degree is a spectator parameter. -/
def middleUnitSeries (R : Type*) [CommRing R] (k A : ℕ) : MvPowerSeries (Fin 3) R :=
  balancedUnitSeries R k A *
    (1-MvPowerSeries.X 2-MvPowerSeries.X 0*MvPowerSeries.X 1*MvPowerSeries.X 2)^k *
    (1-MvPowerSeries.X 2)^k * (1-MvPowerSeries.X 1*MvPowerSeries.X 2)^k

def middleUnit (R : Type*) [CommRing R] (k A : ℕ) : (MvPowerSeries (Fin 3) R)ˣ where
  val := middleUnitSeries R k A
  inv := MvPowerSeries.invOfUnit (middleUnitSeries R k A) 1
  val_inv := MvPowerSeries.mul_invOfUnit _ 1 (by simp [middleUnitSeries,balancedUnitSeries])
  inv_val := MvPowerSeries.invOfUnit_mul _ 1 (by simp [middleUnitSeries,balancedUnitSeries])

/-- Genuine native inverse coefficients at every signed four-index target. -/
def rawMiddleCoefficient (P : MvPowerSeries (Fin 4) R) (k : ℕ)
    (a : Fin 4 → ℕ) (e : Exponent 4) : R :=
  signedExtend ((↑((middleUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R) *
    numeratorSlice P (total e+degree k a)) (W e+middleShift k a)

private def read (b : Exponent 3) (F : ℤ → MvPowerSeries (Fin 3) R) :
    Distribution 4 R := fun e => signedExtend (F (total e)) (W e+b)

private def chartVariables (R : Type*) [CommRing R] : Fin 4 → MvPowerSeries (Fin 3) R :=
  ![1,MvPowerSeries.X 0*MvPowerSeries.X 1*MvPowerSeries.X 2,
    MvPowerSeries.X 2,MvPowerSeries.X 1*MvPowerSeries.X 2]

private theorem variable_transport (b : Exponent 3) (i : Fin 4)
    (F : ℤ → MvPowerSeries (Fin 3) R) :
    polynomialAction (variablePolynomial i) (read b F) =
      read b (fun t => chartVariables R i * F (t-1)) := by
  funext e
  rw [variablePolynomial,polynomialAction,AddMonoidAlgebra.lift_single]
  change (1 : ℂ) • signedExtend (F (total (e-Pi.single i 1)))
    (W (e-Pi.single i 1)+b) =
    signedExtend (chartVariables R i * F (total e-1)) (W e+b)
  rw [one_smul]
  have ht : total (e-Pi.single i 1)=total e-1 := by
    fin_cases i <;> simp [total] <;> ring
  rw [ht]
  fin_cases i
  · dsimp [chartVariables]
    rw [one_mul]
    congr 1
    funext c
    fin_cases c <;> dsimp [W] <;> simp
  · dsimp [chartVariables]
    rw [mul_assoc,mul_assoc,← pow_one (MvPowerSeries.X 0),signed_X_pow_mul,
      ← pow_one (MvPowerSeries.X 1),signed_X_pow_mul,
      ← pow_one (MvPowerSeries.X 2),signed_X_pow_mul]
    congr 1
    funext c
    fin_cases c <;> dsimp [W] <;> simp <;> ring
  · dsimp [chartVariables]
    rw [← pow_one (MvPowerSeries.X 2),signed_X_pow_mul]
    congr 1
    funext c
    fin_cases c <;> dsimp [W] <;> simp <;> ring
  · dsimp [chartVariables]
    rw [mul_assoc,← pow_one (MvPowerSeries.X 1),signed_X_pow_mul,
      ← pow_one (MvPowerSeries.X 2),signed_X_pow_mul]
    congr 1
    funext c
    fin_cases c <;> dsimp [W] <;> simp <;> ring

private theorem add_transport (b : Exponent 3) (n : ℕ) (p q : LaurentPolynomial 4)
    (P Q : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (read b F) = read b (fun t => P * F (t - n)))
    (hq : ∀ F, polynomialAction q (read b F) = read b (fun t => Q * F (t - n)))
    (F : ℤ → MvPowerSeries (Fin 3) R) :
    polynomialAction (p+q) (read b F) = read b (fun t => (P+Q)*F (t-n)) := by
  rw [map_add,LinearMap.add_apply,hp,hq]
  funext e
  change signedExtension (P*F (total e-n)) (W e+b) +
    signedExtension (Q*F (total e-n)) (W e+b) =
      signedExtension ((P+Q)*F (total e-n)) (W e+b)
  rw [add_mul,map_add]
  rfl

private theorem sub_transport (b : Exponent 3) (n : ℕ) (p q : LaurentPolynomial 4)
    (P Q : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (read b F) = read b (fun t => P * F (t - n)))
    (hq : ∀ F, polynomialAction q (read b F) = read b (fun t => Q * F (t - n)))
    (F : ℤ → MvPowerSeries (Fin 3) R) :
    polynomialAction (p-q) (read b F) = read b (fun t => (P-Q)*F (t-n)) := by
  rw [map_sub,LinearMap.sub_apply,hp,hq]
  funext e
  change signedExtension (P*F (total e-n)) (W e+b) -
    signedExtension (Q*F (total e-n)) (W e+b) =
      signedExtension ((P-Q)*F (total e-n)) (W e+b)
  rw [sub_mul,map_sub]
  rfl

private theorem mul_transport (b : Exponent 3) (n m : ℕ) (p q : LaurentPolynomial 4)
    (P Q : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (read b F) = read b (fun t => P * F (t - n)))
    (hq : ∀ F, polynomialAction q (read b F) = read b (fun t => Q * F (t - m)))
    (F : ℤ → MvPowerSeries (Fin 3) R) :
    polynomialAction (p*q) (read b F) = read b (fun t => (P*Q)*F (t-(n+m : ℕ))) := by
  rw [map_mul,Module.End.mul_apply,hq,hp]
  congr 1
  funext t
  rw [mul_assoc]
  apply congrArg (fun t => P*(Q*F t))
  push_cast
  ring

private theorem pow_transport (b : Exponent 3) (n : ℕ) (p : LaurentPolynomial 4)
    (P : MvPowerSeries (Fin 3) R)
    (hp : ∀ F, polynomialAction p (read b F) = read b (fun t => P * F (t - n)))
    (r : ℕ) (F : ℤ → MvPowerSeries (Fin 3) R) :
    polynomialAction (p^r) (read b F) = read b (fun t => P^r*F (t-(n*r : ℕ))) := by
  induction r generalizing F with
  | zero => simp
  | succ r ih =>
    rw [pow_succ',pow_succ',Nat.mul_succ]
    have h := mul_transport b n (n*r) p (p^r) P (P^r) hp ih F
    simpa only [Nat.add_comm] using h

omit [Algebra ℂ R] in
private theorem factorization (S T U : MvPowerSeries (Fin 3) R) (k A B C : ℕ) :
    (S*T*U+U)^A * U^B * (T*U)^C *
      (1-S*T*U-U)^k*(1-U)^k*(1-T*U)^k*(S*T*U)^k *
      (S*T*U+U-T*U)^k*(U-T*U)^k =
    S^k*T^(k+C)*U^(A+B+C+3*k)*
      ((1+S*T)^A*(1+S*T-T)^k*(1-T)^k *
        (1-U-S*T*U)^k*(1-U)^k*(1-T*U)^k) := by
  rw [show S*T*U+U-T*U=(1+S*T-T)*U by ring,
    show S*T*U+U=(1+S*T)*U by ring,
    show U-T*U=(1-T)*U by ring,show 3*k=k+k+k by omega]
  rw [show 1-S*T*U-U=1-U-S*T*U by ring]
  simp only [mul_pow,pow_add]
  ring

private theorem action_chart (F : ℤ → MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 4 → ℕ) (e : Exponent 4) :
    polynomialAction (middlePolynomial k a) (read (middleShift k a) F) e =
      signedExtend (middleUnitSeries R k (a 1)*F (total e-degree k a)) (W e) := by
  let b := middleShift k a
  have hx := variable_transport (R := R) b 0
  have hb := variable_transport (R := R) b 1
  have hz := variable_transport (R := R) b 2
  have hy := variable_transport (R := R) b 3
  have hp := add_transport b 1 _ _ _ _ hb hz
  have ht := sub_transport b 1 _ _ _ _ (sub_transport b 1 _ _ _ _ hx hb) hz
  have hd := sub_transport b 1 _ _ _ _ hx hz
  have he := sub_transport b 1 _ _ _ _ hx hy
  have hc := sub_transport b 1 _ _ _ _ hp hy
  have hf := sub_transport b 1 _ _ _ _ hz hy
  have transport := mul_transport b _ _ _ _ _ _
    (mul_transport b _ _ _ _ _ _
      (mul_transport b _ _ _ _ _ _
        (mul_transport b _ _ _ _ _ _
          (mul_transport b _ _ _ _ _ _
            (mul_transport b _ _ _ _ _ _
              (mul_transport b _ _ _ _ _ _
                (mul_transport b _ _ _ _ _ _
                  (mul_transport b _ _ _ _ _ _
                    (pow_transport b 1 _ _ hx (a 0))
                    (pow_transport b 1 _ _ hp (a 1)))
                  (pow_transport b 1 _ _ hz (a 2)))
                (pow_transport b 1 _ _ hy (a 3)))
              (pow_transport b 1 _ _ ht k))
            (pow_transport b 1 _ _ hd k))
          (pow_transport b 1 _ _ he k))
        (pow_transport b 1 _ _ hb k))
      (pow_transport b 1 _ _ hc k))
    (pow_transport b 1 _ _ hf k) F
  have h := congrFun transport e
  have deg : 1*a 0+1*a 1+1*a 2+1*a 3+1*k+1*k+1*k+1*k+1*k+1*k=degree k a := by
    dsimp [degree]
    omega
  simp only [deg] at h
  change polynomialAction (middlePolynomial k a) (read b F) e = _ at h
  rw [h]
  change signedExtend _ (W e+middleShift k a)=_
  dsimp only [chartVariables]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_pow,one_mul]
  rw [factorization]
  change signedExtend
    ((MvPowerSeries.X 0^k * MvPowerSeries.X 1^(k+a 3) *
      MvPowerSeries.X 2^(a 1+a 2+a 3+3*k) * middleUnitSeries R k (a 1)) *
      F (total e-degree k a)) (W e+middleShift k a)=_
  rw [mul_assoc,mul_assoc,mul_assoc,signed_X_pow_mul,signed_X_pow_mul,signed_X_pow_mul]
  congr 1
  funext i
  fin_cases i <;> dsimp [middleShift,W] <;> simp

omit [Algebra ℂ R] in
private theorem numerator_coeff (P : MvPowerSeries (Fin 4) R) (T : ℤ) (n m t : ℕ) :
    MvPowerSeries.coeff (index3 n m t) (numeratorSlice P T) =
      signedExtend P ![T-t,n,(t : ℤ)-m,(m : ℤ)-n] := by
  classical
  have hc : MvPowerSeries.coeff (index3 n m t) (numeratorSlice P T) =
      if n≤m ∧ m≤t then signedExtend P ![T-t,n,(t : ℤ)-m,(m : ℤ)-n] else 0 := by
    simp [MvPowerSeries.coeff_apply,numeratorSlice,index3]
  rw [hc]
  split_ifs with h
  · rfl
  · rw [signedExtend,ite_eq_right]
    intro he
    have h2 := he 2
    have h3 := he 3
    simp only [Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h2 h3
    omega

private theorem numerator_readout (P : MvPowerSeries (Fin 4) R) (e : Exponent 4) :
    signedExtend (numeratorSlice P (total e)) (W e)=signedExtend P e := by
  classical
  by_cases hw : ∀ i,0≤W e i
  · let n : Fin 3 → ℕ := fun i => (W e i).toNat
    have h0 : (n 0 : ℤ)=e 1 := Int.toNat_of_nonneg (hw 0)
    have h1 : (n 1 : ℤ)=e 1+e 3 := Int.toNat_of_nonneg (hw 1)
    have h2 : (n 2 : ℤ)=e 1+e 3+e 2 := Int.toNat_of_nonneg (hw 2)
    have idx : signedIndex (W e)=index3 (n 0) (n 1) (n 2) := by
      ext i
      fin_cases i <;> simp [signedIndex,index3,n]
    rw [signedExtend,ite_eq_left hw]
    change MvPowerSeries.coeff (signedIndex (W e)) (numeratorSlice P (total e)) = _
    rw [idx]
    rw [numerator_coeff]
    congr 1
    funext i
    fin_cases i <;> simp [total] <;> omega
  · rw [signedExtend,ite_eq_right hw,signedExtend,ite_eq_right]
    intro he
    apply hw
    intro i
    have h1 := he 1
    have h2 := he 2
    have h3 := he 3
    fin_cases i <;> dsimp [W] <;> omega

/-- Native inversion proves the full literal clearing action at all signed indices. -/
theorem raw_middle_action (P : MvPowerSeries (Fin 4) R) (k : ℕ)
    (a : Fin 4 → ℕ) (e : Exponent 4) :
    polynomialAction (middlePolynomial k a) (rawMiddleCoefficient P k a) e =
      signedExtend P e := by
  change polynomialAction (middlePolynomial k a)
    (read (middleShift k a) (fun t =>
      (↑((middleUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R)*
        numeratorSlice P (t+degree k a))) e = _
  rw [action_chart]
  rw [sub_add_cancel,← mul_assoc,
    show middleUnitSeries R k (a 1) *
      (↑((middleUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R)=1 from
        (middleUnit R k (a 1)).val_inv,one_mul,numerator_readout]

/-- Native support is nested; cancellation does not require the actual channel
 to have these particular bounds. -/
theorem raw_middle_support (P : MvPowerSeries (Fin 4) R) (k : ℕ) (a : Fin 4 → ℕ) :
    MiddleSupport (rawMiddleCoefficient P k a) := by
  refine ⟨⟨k,?_⟩,?_,?_⟩
  · intro x b z y h
    apply ite_eq_right
    intro hn
    have hh := hn 0
    dsimp [W,middleShift] at hh
    omega
  · intro b
    refine ⟨(b+k+a 3).toNat,?_⟩
    intro x z y h
    apply ite_eq_right
    intro hn
    have hh := hn 1
    dsimp [W,middleShift] at hh
    have := Int.self_le_toNat (b+k+a 3)
    omega
  · intro b y
    refine ⟨(b+y+a 1+a 2+a 3+3*k).toNat,?_⟩
    intro x z h
    apply ite_eq_right
    intro hn
    have hh := hn 2
    dsimp [W,middleShift] at hh
    have := Int.self_le_toNat (b+y+a 1+a 2+a 3+3*k)
    omega

end
end D5.S3.VertexAlgebra.FourFieldMiddleNativeInverse
