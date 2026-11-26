import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.PartnerAlgebra
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Gauss sums of a character of the determinant over matrix rings. Only
one-dimensional ramified characters are treated, and the exact value is not computed. Only the
eigen-relation, the vanishing at singular index and the modulus are obtained, for matrices over a
finite ring and for scalars over the integers of a product of local fields. Source: T. Kondo, On
Gaussian sums attached to the general linear groups over finite fields, J. Math. Soc. Japan 15
(1963) 244–255; for the scalar case over finite rings, E. Lamprecht, Math. Nachr. 9 (1953), see K.
Conrad, Gauss and Jacobi sums on finite fields and Z/mZ, §4; for the local scalar case, Tate's
thesis §2.5.

This file: Cut-off ramified character: periodic, of norm one on units, locally constant. The cut-off
inverse character is multiplicative on integers. Standard ramified data given by determinants; they
are partners and Schwartz-Bruhat. Local Gauss sum from the residue ring; three-block integral frames
and standard data. Invariance under block translations implies invariance under shears of standard
data. -/

noncomputable section

variable {F} [SemilocalField F] {χ : MulChar F ℂ} [h : TameLocalChar χ]

lemma TameLocalChar.invOnUnits_unif_mul_add {s} (hs : s ∈ SemilocalField.O) x : invOnUnits χ
  (SemilocalField.ϖ.1 * s + x) = invOnUnits χ x := by_cases (by simpa [↓map_add, ← h.resChar_spec.2,
  (h.reduction_spec.2 _).2, *] using h.resChar_spec.2 <| ⟨_, mul_mem SemilocalField.ϖ_mem hs⟩ +
  ⟨x, ·⟩) (by grind [invOnUnits, add_mem_cancel_left, mul_mem, SemilocalField.ϖ_mem])

lemma TameLocalChar.norm_eq_one {t} (u : IsIntegralUnit t) : ‖χ
  t‖ = 1 := by simpa [← h.resChar_spec.2, invOnUnits, u] using (h.resChar.isOfFinOrder
  (((@isIntegralUnit_iff_isUnit _ _ ⟨t, u.1⟩).1 u).map h.reduction).isOfFinOrder).norm_eq_one

lemma TameLocalChar.isLocallyConstant_invOnUnits : IsLocallyConstant (invOnUnits χ) :=
  isLocallyConstant_of_eventually_add (.mono ((SemilocalField.isOpen_O.preimage_of_continuous
  (f := (SemilocalField.ϖ.2 * ·))).mem_nhds (by simp)) fun _ ↦
  (by simpa [add_comm] using h.invOnUnits_unif_mul_add ·))

lemma invOnUnits_mul {F} [V : SemilocalField F] {χ x y} (hx : x ∈ V.O) (hy : y ∈ V.O) :
    invOnUnits χ (x * y) = invOnUnits χ x * invOnUnits χ y := by simp [invOnUnits, ite_and,
  mul_comm x, by simpa [← isIntegralUnit_iff_isUnit] using @IsUnit.mul_iff V.O _ _ ⟨_, hy⟩ ⟨_, hx⟩]

open Matrix SemilocalField schwartzBruhat MeasureTheory Fintype Fint MatMul
variable {F : _} [SemilocalField F] {a b n : Type} [Fintype b] [Fintype n] (e :
  b ⊕ a ≃ n) (χ : MulChar F ℂ) (s : Matrix b n F)

/-- The standard datum of s: y ↦ χ⁻¹(det sy) if y is integral and det sy is a unit of O, and 0
otherwise. -/
def stdColDatum (y : Matrix n b F) := ite (IsIntMatrix O y) (invOnUnits χ (s * y).det) 0

/-- The function x ↦ χ⁻¹(det) of the square matrix with rows those of s and x, ordered by e, if
it lies in GL_n(O); 0 otherwise. -/
def stdRowDatum x := stdColDatum χ 1 ((s.fromRows x).submatrix e.symm id)

/-- A square matrix is primitive (integral with an integral left inverse) if and only if it is
integral and its determinant is a unit of O. -/
lemma isPrimitiveMatrix_iff_isIntegralUnit_det {A : Matrix n n F} : IsPrimitiveMatrix O A ↔
  IsIntMatrix O A ∧ IsIntegralUnit A.det := ⟨fun ⟨a, _, b, c⟩ ↦
  ⟨a, a.det_mem, _, b.det_mem, by simp [← det_mul, c]⟩, fun ⟨a, _, _, b, _⟩ ↦
  ⟨a, _, a.adjugate.smul b, by simp [adjugate_mul, smul_smul, *]⟩⟩

variable {χ s} {Ψ : Matrix n b F → ℂ}

omit [Fintype b] in
lemma Membership.mem.transpose_mem_schwartzBruhat : Ψ ∈ schwartzBruhat HasLeftInv →
  (Ψ ·ᵀ) ∈ schwartzBruhat (HasLeftInv ·ᵀ) := (comp · _ fun _ ↦ id)

lemma schwartzBruhat.of_support_primitive (h : IsLocallyConstant Ψ) (hs : ∀ y, Ψ y ≠ 0 →
  IsPrimitiveMatrix O y) : Ψ ∈ schwartzBruhat HasLeftInv :=
  ⟨h, isCompact_O.matrix.closure_of_subset (hs · · |>.1), (hs · · |>.2.imp (by simp))⟩

lemma invOnUnits_eq_mul_of_unit {t x} (h : IsIntegralUnit t) : invOnUnits χ x = χ t * invOnUnits χ
  (x * t) := by grind [invOnUnits_mul, invOnUnits, χ.map_one, → mul_mem h.2.choose_spec.1]

lemma isIntMatrix_of_stdColDatum_ne_zero (hs : IsIntMatrix O s) {y} : stdColDatum χ s y ≠ 0 →
  IsIntMatrix O y ∧ IsPrimitiveMatrix O (s * y) := by
  grind [stdColDatum, invOnUnits, isPrimitiveMatrix_iff_isIntegralUnit_det, hs.mul]

lemma isPrimitiveMatrix_of_stdColDatum_ne_zero (hs : IsIntMatrix O s) y : stdColDatum χ s y ≠ 0 →
  IsPrimitiveMatrix O y := .imp_right (fun ⟨_, t, k, _⟩ ↦
  ⟨_, k.mul hs, by rwa [t.mul_assoc]⟩) ∘ isIntMatrix_of_stdColDatum_ne_zero hs

lemma isPartner_stdRowDatum_stdColDatum [Fintype a]
    (hs : IsIntMatrix O s) : IsPartner O e χ (stdRowDatum e χ s)
  (stdColDatum χ s) := ⟨fun x h ↦ (isPrimitiveMatrix_iff.1 (isIntMatrix_of_stdColDatum_ne_zero .one
  h).2).imp' (·⁻¹) (by aesop), ((valPair.exists_firstCols_iff e).2 ∘
  isPrimitiveMatrix_of_stdColDatum_ne_zero hs ·), fun k h ↦ by simp_all [stdRowDatum, stdColDatum,
  IsIntMatrix, mem_intGL, reindex_equiv e, ← det_fromRows_invLastRows, ← invOnUnits_eq_mul_of_unit,
  isPrimitiveMatrix_iff_isIntegralUnit_det.1 ((isPrimitiveMatrix_iff_mem_intGL k).2 h)]⟩

variable (χ) [hχ : TameLocalChar χ]

lemma stdColDatum_mem_schwartzBruhat (hs : IsIntMatrix O s) :
  stdColDatum χ s ∈ schwartzBruhat HasLeftInv := of_support_primitive (LocallyConstant.indicator ⟨_,
  hχ.isLocallyConstant_invOnUnits.comp_continuous (by fun_prop)⟩ ⟨isCompact_O.matrix.isClosed,
  isOpen_O.matrix⟩).2 (isPrimitiveMatrix_of_stdColDatum_ne_zero hs)

omit [Fintype b] in
/-- For tame χ, the function `stdRowDatum` e χ s is locally constant with compact support in the
matrices that have a right inverse. -/
lemma stdRowDatum_mem : stdRowDatum e χ s ∈ schwartzBruhat (HasLeftInv ·ᵀ) :=
  comp (stdColDatum_mem_schwartzBruhat χ .one) _ (fun _ ⟨_, h⟩ ↦ hasLeftInv_invLastRows_transpose e
  (.mkOfMulEqOne _ _ h)) (continuous_matrix ((reindex_equiv e).1.2 (by
    rintro (_ | _) _ <;> simp <;> fun_prop)))

variable (F : _) [SemilocalField F] (m n p a : Type) [Fintype m] [Fintype n] [Fintype p] {χ : _}

/-- An integral invertible matrix over F cut into column blocks (K I L), with its integral
inverse cut into row blocks K′, I′, L′. -/
structure IntegralFrame where
  (K L : Matrix m p F) (I : Matrix m n F) (K' L' : Matrix p m F) (I' : Matrix n m F)
  spec : let P := fromCols K (fromCols I L); let Q := fromRows K' (fromRows I' L')
    IsIntMatrix O P ∧ IsIntMatrix O Q ∧ P * Q = 1 ∧ Q * P = 1

variable {F m n p a} (A : IntegralFrame F m n p)

omit [Fintype p] in
@[simp] lemma submatrix_id_mul {c} (f : c → a) (M : Matrix a n F) (N : Matrix n p F) :
    M.submatrix f id * N = (M * N).submatrix f id := rfl

/-- Gauss sums: for ψ continuous, unitary, of conductor O and χ tamely ramified at each factor,
the integral of χ⁻¹(x)ψ(tx) over O^× is γχ(ϖt) if ϖt is a unit and 0 otherwise, with |γ|² =
vol(ϖO).

Known result: Gauss sums of a character of the determinant over matrix rings. -/
lemma exists_local_gauss_sum (hχ : TameLocalChar χ) {ψ} (hψ : HasIntegralConductor ψ) :
  ∃ γ, ‖γ‖ ^ 2 = (Nat.card hχ.ResidueRing : ℝ)⁻¹ ∧ ∀ t : F, ∫ x in ‹SemilocalField F›.O,
  invOnUnits χ x * ψ (t * x) = γ / invOnUnits χ (ϖ.1 * t) := by
  obtain ⟨⟨φ, p, e⟩, _, r, d⟩ := exists_primitive_residue_addChar hχ.reduction_spec hψ.2,
    hχ.isLocallyConstant_invOnUnits.continuous, hχ.resChar_spec
  obtain ⟨⟨E, N⟩, _, w⟩ :=
    matrix_gauss_sum (a := Unit) p r (hχ.resChar ·.det) (by simp [↓det_mul]), hψ
  use ?_ / card hχ.ResidueRing, by simpa [card_congr uniqueEquiv, field] using congr(‖$N‖),
    fun t ↦ ?_
  have T (s : O.toAddSubgroup) := setIntegral_add_mem (ν :=
    volume) (invOnUnits χ * (ψ <| t * ·)) s.2
  by_cases k : ϖ.1 * t ∈ O
  simpa [← d, hχ.resChar.inv_apply_eq_inv', field, volume_O, Measure.real, mul_comm] using
    ((integral_finsetSum _ fun r _ ↦ isCompact_O.integrableOn _).trans
    congr(∑ r, $(T (hχ.reduction_spec.1 r).choose))).symm.trans (setIntegral_congr_fun
    isCompact_O.measurableSet fun x hx ↦
    .trans (sum_equiv (.trans (.addRight (hχ.reduction ⟨x, hx⟩)) uniqueEquiv.symm) _ _ fun r ↦ by
    nth_rw 3 4 [← (hχ.reduction_spec.1 r).choose_spec]
    simp [trace, ← map_add, ← map_mul, e, ← d, mul_assoc]) (E (hχ.reduction ⟨_, k⟩ • 1)))
  refine (by_contra fun h ↦ k ((w _).1 fun s a ↦
    (mul_eq_right₀ h).1 ?_)).trans (by grind [invOnUnits])
  simpa [hχ.invOnUnits_unif_mul_add a, mul_add, ψ.map_add_eq_mul, ← integral_const_mul,
    mul_left_comm, mul_assoc] using T ⟨_, O.mul_mem ϖ_mem a⟩

lemma IntegralFrame.blocks_spec : IsIntMatrix O A.L' ∧ IsIntMatrix O A.I' ∧ IsIntMatrix O A.K ∧
  IsIntMatrix O A.L ∧ IsIntMatrix O A.K' ∧ IsIntMatrix O A.I ∧ A.K' * A.K = 1 ∧ A.I' * A.K = 0 ∧
  A.L' * A.K = 0 ∧ A.K' * A.I = 0 ∧ A.I' * A.I = 1 ∧ A.L' * A.I = 0 ∧ A.K' * A.L = 0 ∧
  A.I' * A.L = 0 ∧ A.L' * A.L = 1 := A.7.rec (by simp_all [← ext_iff, IsIntMatrix])

/-- The function of a matrix x equal to G(x·(K I)) if x is integral and 0 otherwise. -/
def IntegralFrame.stdDatum (G : _ → ℂ) (x : Matrix a m F) :=
  ite (IsIntMatrix O x) (G (x * A.K.fromCols A.I)) 0

/-- Let s be integral, u a column, r a row, su = 0, ru = 0. If the linear form Λ is invariant,
on a space M of Schwartz–Bruhat functions, under all y ↦ y + u·z·s·y, it agrees on Ψ_s =
`stdColDatum` and on Ψ_s(y + u·r·y) when both lie in M. -/
lemma shear_invariant {F b n} [V : SemilocalField F] [Fintype b] [Fintype n] {χ M U} {s :
  Matrix b n F} (hs : IsIntMatrix O s) {u : Matrix n Unit F} {r : Matrix Unit n F} (h₁ : s * u = 0
  ∧ r * u = 0) {Λ : _ →ₗ[ℂ] ℂ} (hM : M ≤ schwartzBruhat U) (h : ∀ Ψ ∈ M, ∀ z : Matrix Unit b F,
  (Λ fun y ↦ Ψ (y + u * (z * (s * y)))) = Λ Ψ) : let Ψ y := stdColDatum χ s (y + u * (r * y))
  stdColDatum χ s ∈ M → Ψ ∈ M → Λ Ψ = Λ (stdColDatum χ s) := fun p q ↦ by
  let S := @V.O.toAddSubgroup.matrix n b
  let τ (t : S) (y : Matrix n b F) := y + u * (r * t.1 * (s * y))
  have : CompactSpace S := isCompact_O.matrix.compactSpace
  have K {Ψ} a : _ = Λ Ψ := (integral_mem_of_isLocallyConstant _
    ((schwartzBruhat.isLocallyConstant_curry (hM a) τ (τ <| -·) (by simp [τ, *,
    ← s.mul_assoc])).comp (Option.elim' _)) (P := (Λ ∘ₗ .funLeft _ _ some).eqLocus
    (.proj none)) (by bound)).trans (average_const .addHaar _)
  use K q ▸ K p ▸ congr(Λ fun y ↦ $((em' (∃ ρ : Matrix Unit b F,
    stdColDatum χ s (y + u * ρ) ≠ 0)).elim (by simp_all [τ, add_assoc, ← Matrix.mul_add]) fun ⟨ρ,
    k⟩ ↦ (isIntMatrix_of_stdColDatum_ne_zero hs k).elim fun i ⟨_, g, m, _⟩ ↦ .trans (by simp_all [τ,
    ← Matrix.mul_assoc _ u, add_assoc]) (integral_add_right_eq_self _ ⟨_, i.mul m⟩)))
