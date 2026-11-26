import GRH.Lib.General.Geometry.EtaleCharts
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck symbols)
(known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Projective space as functor with standard atlas; a map P^d×P¹ to P^{d+1}. Functions
cutting out the locus where two points agree; basic properties. -/

open CategoryTheory CommAlgCat Fin Ideal MvPolynomial Set MonoidalCategory RingHom

attribute [local simp] mem_span_singleton span_le Units.smul_def _root_.funext_iff

variable (k) [Field k] (d) {A : CommAlg k} {v w : Fin (d + 1) → A} {h : span (range v) = ⊤}

/-- For a field k, projective d-space as the functor sending A to the unimodular vectors in
A^{d+1} modulo units of A. -/
def projSpace : CommAlg k ⥤ Type 1 := by refine ⟨fun A ↦ Quot ((MulAction.orbitRel Aˣ _).comap
  (·.1.1 : @unimodular k _ (d + 1) A → _)), fun f ↦ ↾.map (unimodular.toFunctor.map f) fun _ _ ⟨u,
  h⟩ ↦ ⟨u.map _, by simpa using! congr(f ∘ $h)⟩, ?_, ?_⟩ <;> intros <;> ext ⟨⟩ <;> rfl

variable {k d}

lemma projSpace.exists_isUnit_of_span_eq_top [IsLocalRing A] (h : span (Set.range v) = ⊤) : ∃ i,
  IsUnit (v i) := by simpa [← h] using (IsLocalRing.maximalIdeal.isMaximal A).lt_top.not_ge

/-- For v in A^{d+1} whose entries generate the unit ideal, the point [v_0 : … : v_d] of
projective d-space. -/
def projSpace.mk (v : Fin (d + 1) → A) (h : span (Set.range v) = ⊤) : projSpace k d A :=
  .mk _ ⟨_, h⟩

lemma projSpace.mk_eq_mk_iff_exists_unit {h'} : mk v h = mk w h' ↔ ∃ u : Aˣ, u • v = w :=
  eq_comm.trans Quotient.eq

lemma projSpace.mk_eq_mk_iff_cross_mul {h'} : mk v h = mk w h' ↔ ∀ a b, v a * w b = w a * v b :=
  mk_eq_mk_iff_exists_unit.trans ⟨by
  simp; grind, fun e ↦ have ⟨a, ha⟩ := mem_span_range_iff_exists_fun.1 (h.ge (x := 1) ⟨⟩)
  have E l := by simpa [← mul_assoc, ← Finset.sum_mul, ha] using congr(∑ i, a i * $(e i l))
  ⟨(span_singleton_eq_top.1 (eq_top_mono (by simpa using (⟨_, E ·⟩)) h')).unit, (funext E).symm⟩⟩

/-- For a k-algebra A, an index i and v in A^d, the A-point of projective d-space with
homogeneous coordinates v and 1 inserted at position i. -/
abbrev projSpace.affinePoint i v :=
  @mk k _ d A (i.insertNth 1 v) (span_eq_top_of_isUnit i (by simp))

lemma projSpace.mk_mem_stdChart_iff i : mk v h ∈ Subfunctor.range
  (pointMap (affinePoint (A := of k (MvPolynomial _ k)) i X)) A ↔ IsUnit (v i) :=
  ⟨fun ⟨φ, e⟩ ↦ (mk_eq_mk_iff_exists_unit.1 e).rec (by aesop), fun ⟨u, e⟩ ↦ ⟨⟨ofHom (aeval
  (u⁻¹ • v ∘ i.succAbove))⟩, mk_eq_mk_iff_exists_unit.2 ⟨u, by simp [i.forall_iff_succAbove, ← e]⟩⟩⟩

variable [CharZero k]

lemma projSpace.exists_eq_single_of_mul_eq_zero [IsLocalRing A] {w : Fin 2 → A} H hw (h : ∀ i,
  (w 1 - i * w 0) * v i = 0) : IsUnit (w 0 * ∑ i, v i) ∧ ∃ j, (mk v H, mk w hw) =
  (_ ⊗ projSpace k 1).map structureMap (affinePoint j 0, affinePoint 0 ![j]) := by
  have ⟨j, J⟩ := exists_isUnit_of_span_eq_top H
  have e := J.mul_left_eq_zero.1 (h j)
  obtain ⟨_, u⟩ := by simpa [sub_eq_zero.1 e, or_and_left] using exists_isUnit_of_span_eq_top hw
  have z i (m : v i ≠ 0) : i = j := Fin.ext (Nat.cast_injective
    (smul_left_injective k m (u.mul_left_cancel (by grind [Nat.cast_smul_eq_nsmul]))))
  use u.mul (by grind [Fintype.sum_eq_single j]),
    j; ext <;> erw [mk_eq_mk_iff_cross_mul] <;> simp <;> grind

variable (k d)

/-- For 0 ≤ i ≤ d, the standard chart of projective d-space where the i-th coordinate is
invertible, on the polynomial ring in d variables. -/
noncomputable def projSpace.stdChart (i : Fin (d + 1)) : EtaleChart d (projSpace k d) :=
  ⟨_, _, X, by simpa using .containsIdentities _,
  fun _ _ _ h ↦ by ext; simpa using mk_eq_mk_iff_cross_mul.1 h (i.succAbove _) i,
  fun _ ↦ Quot.ind (⟨span {·.1.1 i}, fun _ _ ↦ (mk_mem_stdChart_iff i).trans (by simp)⟩)⟩

instance projSpace.hasAtlas : HasAtlas d (projSpace k d) :=
  {exists_finite_charts := ⟨_, stdChart k d, fun _ h ↦ let := h.toField
  Quot.ind (exists_isUnit_of_span_eq_top ·.2 |>.imp (mk_mem_stdChart_iff · |>.2))⟩,
   exists_ideal := by rintro _ ⟨⟨⟨v⟩⟩⟩ ⟨⟨⟨w⟩⟩⟩; exact ⟨⨆
     (a) (b), span {v a * w b - w a * v b}, fun _ _ ↦ mk_eq_mk_iff_cross_mul.trans (by simp)⟩}

/-- In characteristic 0, the map P^d × P^1 → P^{d+1} sending ([v],[w_0 : w_1]) to [w_0 ∑ v_i :
(w_1 − i w_0)v_i, i = 0, …, d]. -/
def projSpace.lineProductMap : projSpace k d ⊗ projSpace k 1 ⟶ projSpace k d.succ := by refine
  ⟨fun A ↦ ↾fun x ↦ x.1.liftOn₂ x.2 (fun ⟨⟨v⟩, a⟩ ⟨⟨w⟩, b⟩ ↦ mk (cons (w 0 * ∑ i, v i) fun i ↦
  (w 1 - i * w 0) * v i) ((span _).map_id.symm.trans ((map_eq_top_iff_fields _ (𝟙 A)).2 fun K ψ
  h ↦ let := h.toField; by simpa [-not_and, not_and', insert_subset_iff] using!
    (exists_eq_single_of_mul_eq_zero (unimodular.map ψ a) (unimodular.map ψ b) · |>.1))))
  ?_ ?_, ?_⟩ <;> (first | rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ ⟨c, rfl⟩ | intros; ext ⟨⟨⟩, ⟨⟩⟩)
  <;> erw [mk_eq_mk_iff_cross_mul] <;> simp [forall_fin_succ, ← Finset.mul_sum] <;> grind

variable {k : _} [Field k] {X} {d : _} {R K : CommAlg k} {g : Fin d → R} {x P s}

lemma eq_comp_structureMap_of_ker_le {ζ : R ⟶ _} {φ : R ⟶ K} (h : ker ζ.hom ≤ ker φ.hom) : φ =
  ζ ≫ structureMap := by ext r; simpa using @h (r - algebraMap _ _ (ζ r))

/-- The elements f_i of R cut out the locus P at x in X(R): a map of k-algebras α: R → C kills
all f_i exactly when α(x) satisfies P. -/
def CutsOutLocus (X : CommAlg k ⥤ Type 1) (P : ∀ _, _ → _) x (f : Fin d → R) :=
  ∀ C α, span (range f) ≤ ker α.hom ↔ P C (@X.map R C α x)

lemma mem_offPoints_iff [IsSepFunctor X] (l : IsField K) : x ∈ offPoints s K ↔
  ¬@ComesFromPoints _ _ X s K x := ⟨(X.map_id_apply _ x ▸ · _ _ l), fun H _ φ m ⟨z, e, q⟩ ↦
  mem_offDiagonal_of_ne l (H ⟨z, e, ·⟩) _ _ m (map_map_structureMap φ z ▸ q)⟩

lemma CutsOutLocus.preimage_fieldLocus_not (h : CutsOutLocus X P x g) :
  (fieldLocus (¬P · ·)).preimage (pointMap x) = unimodular.preimage (pointMap ⟨g⟩) :=
  by ext; simpa [↓h _, ← range_comp] using! (map_eq_top_iff_fields (span (range g)) _).symm
