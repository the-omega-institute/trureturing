/- GID: D5/S3/Quantum/Algebra/AnticommutingInvariantPlane
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/AnticommutingInvariantPlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Anticommuting selfadjoint involutions construct an actual closed orthonormal plane. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.CStarAlgebra.Spectrum
import D5.S3.Quantum.Algebra.TopologicalSchur
import D5.S3.Quantum.Algebra.PBActualOuterBudget

/-! Actual two-vector planes for bounded anticommuting involutions. -/

noncomputable section
open scoped InnerProductSpace CStarAlgebra

namespace D5.S3.Quantum.Algebra.AnticommutingInvariantPlane

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- The two vectors are constructed in the original Hilbert space. -/
private theorem exists_closed_plane (A B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAA : A * A = 1) (hBB : B * B = 1) (hAB : A * B = -(B * A)) :
    ∃ v w : H, ‖v‖ = 1 ∧ ‖w‖ = 1 ∧ inner ℂ v w = 0 ∧
      A v = v ∧ A w = -w ∧ B v = w ∧ B w = v ∧
      IsClosed (Submodule.span ℂ ({v, w} : Set H) : Set H) ∧
      (∀ x ∈ Submodule.span ℂ ({v, w} : Set H),
        A x ∈ Submodule.span ℂ ({v, w} : Set H) ∧
        B x ∈ Submodule.span ℂ ({v, w} : Set H)) := by
  have hAA' (x : H) : A (A x) = x := by
    simpa using congrArg (fun T : H →L[ℂ] H => T x) hAA
  have hBB' (x : H) : B (B x) = x := by
    simpa using congrArg (fun T : H →L[ℂ] H => T x) hBB
  have hAB' (x : H) : A (B x) = -B (A x) := by
    simpa using congrArg (fun T : H →L[ℂ] H => T x) hAB
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  obtain ⟨v, hv, hAv⟩ := PBActualOuterBudget.supporting_vector
    (A.toLinearMap.restrictScalars ℝ) (B.toLinearMap.restrictScalars ℝ)
    hAA' hBB' hAB'
  let w : H := B v
  have hBw : B w = v := hBB' v
  have hAw : A w = -w := by simp [w, hAB', hAv]
  have hBU : B ∈ unitary (H →L[ℂ] H) := by
    rw [Unitary.mem_iff, hB.star_eq, hBB]
    exact ⟨rfl, rfl⟩
  have hw : ‖w‖ = 1 := (Unitary.norm_map ⟨B, hBU⟩ v).trans hv
  have hvw : inner ℂ v w = 0 := by
    have hi := hA.isSymmetric v w
    change inner ℂ (A v) w = inner ℂ v (A w) at hi
    rw [hAv, hAw, inner_neg_right] at hi
    have : (2 : ℂ) * inner ℂ v w = 0 := by linear_combination hi
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  let W := Submodule.span ℂ ({v, w} : Set H)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine ⟨v, w, hv, hw, hvw, hAv, hAw, rfl, hBw, ?_, ?_⟩
  · exact W.closed_of_finiteDimensional
  · intro y hy
    obtain ⟨c, e, rfl⟩ := Submodule.mem_span_pair.mp hy
    have hvW : v ∈ W := Submodule.subset_span (by simp)
    have hwW : w ∈ W := Submodule.subset_span (by simp)
    constructor
    · simpa only [map_add, map_smul, hAv, hAw] using
        W.add_mem (W.smul_mem c hvW) (W.smul_mem e (W.neg_mem hwW))
    · simpa only [map_add, map_smul, hBw, show B v = w from rfl] using
        W.add_mem (W.smul_mem c hwW) (W.smul_mem e hvW)

private def reducingAlgebra (W : Submodule ℂ H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | ∀ x ∈ W, T x ∈ W ∧ (star T) x ∈ W}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro T R hT hR x hx
    simpa only [add_apply, star_add] using
      And.intro (W.add_mem (hT x hx).1 (hR x hx).1)
        (W.add_mem (hT x hx).2 (hR x hx).2)
  mul_mem' := by
    intro T R hT hR x hx
    simpa only [mul_apply_eq_comp, star_mul] using
      And.intro (hT (R x) (hR x hx).1).1 (hR (star T x) (hT x hx).2).2
  algebraMap_mem' := by
    intro c x hx
    simpa [Algebra.algebraMap_eq_smul_one] using
      And.intro (W.smul_mem c hx) (W.smul_mem (star c) hx)
  star_mem' := by
    intro T hT x hx
    simpa only [star_star] using (hT x hx).symm

private theorem reducingAlgebra_closed (W : Submodule ℂ H) (hW : IsClosed (W : Set H)) :
    IsClosed (reducingAlgebra W : Set (H →L[ℂ] H)) := by
  change IsClosed {T : H →L[ℂ] H | ∀ x ∈ W, T x ∈ W ∧ star T x ∈ W}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro hx
  exact (hW.preimage (ContinuousLinearMap.apply ℂ H x).continuous).inter
    (hW.preimage ((ContinuousLinearMap.apply ℂ H x).continuous.comp continuous_star))

/-- Closed-subspace irreducibility turns the explicit plane into the whole Hilbert space.
The third operator is specified by its scalar product formula, rather than by coordinates. -/
private theorem exists_coordinates_of_scalar_product (A B C : H →L[ℂ] H) (z : ℝ)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
    (hAA : A * A = 1) (hBB : B * B = 1) (hAB : A * B = -(B * A))
    (hCeq : C = (-(Complex.I * (z : ℂ))) • (A * B))
    (hirr : ∀ K : ClosedSubmodule ℂ H,
      (∀ T ∈ (StarAlgebra.adjoin ℂ ({A, B, C} : Set (H →L[ℂ] H))).topologicalClosure,
        K.toSubmodule ∈ Module.End.invtSubmodule (T : Module.End ℂ H)) →
      K = ⊥ ∨ K = ⊤) :
    ∃ U : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2),
      (∀ x, U (A x) 0 = U x 0 ∧ U (A x) 1 = -U x 1) ∧
      (∀ x, U (B x) 0 = U x 1 ∧ U (B x) 1 = U x 0) ∧
      (∀ x, U (C x) 0 = -(Complex.I * (z : ℂ)) * U x 1 ∧
        U (C x) 1 = (Complex.I * (z : ℂ)) * U x 0) := by
  classical
  obtain ⟨v, w, hv, hw, hvw, hAv, hAw, hBv, hBw, hclosed, hinv⟩ :=
    exists_closed_plane A B hA hB hAA hBB hAB
  let W := Submodule.span ℂ ({v, w} : Set H)
  have hcInv : ∀ x ∈ W, C x ∈ W := by
    intro x hx
    rw [hCeq, smul_apply, mul_apply_eq_comp]
    exact W.smul_mem _ (hinv _ (hinv x hx).2).1
  have hgen : ({A, B, C} : Set (H →L[ℂ] H)) ⊆ reducingAlgebra W := by
    intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl | rfl
    · intro x hx; simpa only [hA.star_eq] using And.intro (hinv x hx).1 (hinv x hx).1
    · intro x hx; simpa only [hB.star_eq] using And.intro (hinv x hx).2 (hinv x hx).2
    · intro x hx; simpa only [hC.star_eq] using And.intro (hcInv x hx) (hcInv x hx)
  have hle := StarSubalgebra.topologicalClosure_minimal
    (StarAlgebra.adjoin_le hgen) (reducingAlgebra_closed W hclosed)
  have hWtop : W = ⊤ := by
    rcases hirr ⟨W, hclosed⟩ (fun T hT =>
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2
        (fun x hx => (hle hT x hx).1)) with hb | ht
    · have hvW : v ∈ (⟨W, hclosed⟩ : ClosedSubmodule ℂ H) :=
        Submodule.subset_span (by simp)
      rw [hb] at hvW
      have : v = 0 := hvW
      simpa [this] using hv
    · exact congrArg ClosedSubmodule.toSubmodule ht
  let f : Fin 2 → H := ![v, w]
  have hon : Orthonormal ℂ f := by
    simp [f, orthonormal_vecCons_iff, hv, hw, hvw]
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    have hr : Set.range f = ({v, w} : Set H) := by
      ext x; simp [f, or_comm]
    rw [hr, ← hWtop]
  let ob := OrthonormalBasis.mk hon hsp
  have he0 (x : H) : ob.repr x 0 = inner ℂ v x := by
    simp [OrthonormalBasis.repr_apply_apply, ob, f]
  have he1 (x : H) : ob.repr x 1 = inner ℂ w x := by
    simp [OrthonormalBasis.repr_apply_apply, ob, f]
  have ha0 (x : H) : ob.repr (A x) 0 = ob.repr x 0 := by
    simp only [he0]
    have hi := hA.isSymmetric v x
    change inner ℂ (A v) x = inner ℂ v (A x) at hi
    rw [hAv] at hi
    exact hi.symm
  have ha1 (x : H) : ob.repr (A x) 1 = -ob.repr x 1 := by
    simp only [he1]
    have hi := hA.isSymmetric w x
    change inner ℂ (A w) x = inner ℂ w (A x) at hi
    rw [hAw, inner_neg_left] at hi
    exact hi.symm
  have hb0 (x : H) : ob.repr (B x) 0 = ob.repr x 1 := by
    simp only [he0, he1]
    have hi := hB.isSymmetric v x
    change inner ℂ (B v) x = inner ℂ v (B x) at hi
    rw [hBv] at hi
    exact hi.symm
  have hb1 (x : H) : ob.repr (B x) 1 = ob.repr x 0 := by
    simp only [he0, he1]
    have hi := hB.isSymmetric w x
    change inner ℂ (B w) x = inner ℂ w (B x) at hi
    rw [hBw] at hi
    exact hi.symm
  refine ⟨ob.repr, (fun x => ⟨ha0 x, ha1 x⟩), (fun x => ⟨hb0 x, hb1 x⟩), ?_⟩
  intro x
  rw [hCeq, smul_apply, mul_apply_eq_comp, map_smul]
  constructor
  · change -(Complex.I * (z : ℂ)) * ob.repr (A (B x)) 0 = _
    rw [ha0, hb0]
  · change -(Complex.I * (z : ℂ)) * ob.repr (A (B x)) 1 = _
    rw [ha1, hb1, neg_mul_neg]

private theorem commute_closed_generated (A B C J : H →L[ℂ] H)
    (hJ : IsSelfAdjoint J) (hJA : Commute J A) (hJB : Commute J B) (hJC : Commute J C) :
    ∀ T ∈ (StarAlgebra.adjoin ℂ ({A, B, C} : Set (H →L[ℂ] H))).topologicalClosure,
      Commute J T := by
  have hgen : ({A, B, C} : Set (H →L[ℂ] H)) ⊆ StarSubalgebra.centralizer ℂ {J} := by
    intro T hT
    change T ∈ StarSubalgebra.centralizer ℂ {J}
    apply (StarSubalgebra.mem_centralizer_iff ℂ).2
    intro g hg
    have hgJ : g = J := Set.mem_singleton_iff.mp hg
    subst g
    rw [hJ.star_eq]
    suffices Commute J T from ⟨this.eq, this.eq⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl | rfl
    · exact hJA
    · exact hJB
    · exact hJC
  have hle := StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hgen)
    (show IsClosed (StarSubalgebra.centralizer ℂ {J} : Set (H →L[ℂ] H)) from
      Set.isClosed_centralizer _)
  intro T hT
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hT) J (by simp)).1

/-- A pairwise anticommuting selfadjoint triple with two involutive axes has
simultaneous Pauli coordinates under closed-subspace irreducibility. -/
private theorem exists_coordinates (A B C : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C)
    (hAA : A * A = 1) (hBB : B * B = 1)
    (hAB : A * B = -(B * A)) (hAC : A * C = -(C * A)) (hBC : B * C = -(C * B))
    (hirr : InnerProductSpace.IsTopologicallyIrreducible
      ((StarAlgebra.adjoin ℂ ({A, B, C} : Set (H →L[ℂ] H))).topologicalClosure :
        Set (H →L[ℂ] H))) :
    ∃ (z : ℝ) (U : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2)),
      (∀ x, U (A x) 0 = U x 0 ∧ U (A x) 1 = -U x 1) ∧
      (∀ x, U (B x) 0 = U x 1 ∧ U (B x) 1 = U x 0) ∧
      (∀ x, U (C x) 0 = -(Complex.I * (z : ℂ)) * U x 1 ∧
        U (C x) 1 = (Complex.I * (z : ℂ)) * U x 0) := by
  have hBA : B * A = -(A * B) := by rw [hAB, neg_neg]
  have hCA : C * A = -(A * C) := by rw [hAC, neg_neg]
  have hCB : C * B = -(B * C) := by rw [hBC, neg_neg]
  have hrev : C * B * A = -(A * B * C) := by
    calc
      C * B * A = -(B * (C * A)) := by rw [hCB]; noncomm_ring
      _ = B * (A * C) := by rw [hCA]; noncomm_ring
      _ = -(A * B * C) := by rw [← mul_assoc, hBA]; noncomm_ring
  let J := Complex.I • (A * B * C)
  have hJ : IsSelfAdjoint J := by
    change star J = J
    simp only [J, star_smul, star_mul, hA.star_eq, hB.star_eq, hC.star_eq,
      ← mul_assoc, hrev, Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
  have hJA : Commute J A := by
    change J * A = A * J
    simp only [J, smul_mul_assoc, mul_smul_comm]
    congr 1
    calc
      A * B * C * A = A * (B * (C * A)) := by noncomm_ring
      _ = -(A * (B * (A * C))) := by rw [hCA]; noncomm_ring
      _ = A * (A * B * C) := by rw [← mul_assoc B A C, hBA]; noncomm_ring
  have hJB : Commute J B := by
    change J * B = B * J
    simp only [J, smul_mul_assoc, mul_smul_comm]
    congr 1
    calc
      A * B * C * B = -(A * B * B * C) := by rw [mul_assoc (A * B) C B, hCB]; noncomm_ring
      _ = (B * A) * B * C := by rw [hBA]; noncomm_ring
      _ = B * (A * B * C) := by noncomm_ring
  have hJC : Commute J C := by
    change J * C = C * J
    simp only [J, smul_mul_assoc, mul_smul_comm]
    congr 1
    calc
      A * B * C * C = -(A * C * B * C) := by rw [mul_assoc A B C, hBC]; noncomm_ring
      _ = (C * A) * B * C := by rw [hCA]; noncomm_ring
      _ = C * (A * B * C) := by noncomm_ring
  obtain ⟨z, hz⟩ := InnerProductSpace.exists_eq_algebraMap_of_isSelfAdjoint_of_commute
    hirr hJ (commute_closed_generated A B C J hJ hJA hJB hJC)
  have hprod : (A * B) * (A * B) = -1 := by
    calc
      (A * B) * (A * B) = A * (B * A) * B := by noncomm_ring
      _ = -(A * A) * (B * B) := by rw [hBA]; noncomm_ring
      _ = -1 := by rw [hAA, hBB]; simp
  have hCeq : C = (-(Complex.I * ((-z : ℝ) : ℂ))) • (A * B) := by
    have he := congrArg (fun T : H →L[ℂ] H => (Complex.I • (A * B)) * T) hz
    have hleft : (Complex.I • (A * B)) * J = C := by
      simp only [J, smul_mul_smul_comm, ← mul_assoc, hprod]
      simp [Complex.I_mul_I]
    rw [hleft, Algebra.algebraMap_eq_smul_one] at he
    simp only [mul_smul_comm, mul_one, smul_smul] at he
    simpa [← Complex.coe_smul, smul_smul, mul_comm] using he
  obtain ⟨U, hU⟩ := exists_coordinates_of_scalar_product A B C (-z)
    hA hB hC hAA hBB hAB hCeq hirr
  exact ⟨-z, U, hU⟩

private theorem normalized_irreducible {R : Type*} [CStarAlgebra R]
    (π : R →⋆ₐ[ℂ] (H →L[ℂ] H)) (a b d : R) (X Y : ℝ)
    (hX : X ≠ 0) (hY : Y ≠ 0)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hd : IsSelfAdjoint d)
    (hgen : (StarAlgebra.adjoin ℂ ({a, b, d} : Set R)).topologicalClosure = ⊤)
    (hirr : InnerProductSpace.IsTopologicallyIrreducible (Set.range π)) :
    InnerProductSpace.IsTopologicallyIrreducible
      ((StarAlgebra.adjoin ℂ ({(X⁻¹ : ℝ) • π a, (Y⁻¹ : ℝ) • π b, π d} :
        Set (H →L[ℂ] H))).topologicalClosure : Set (H →L[ℂ] H)) := by
  intro K hK
  apply hirr K
  have hmem (T : H →L[ℂ] H)
      (hT : T ∈ ({(X⁻¹ : ℝ) • π a, (Y⁻¹ : ℝ) • π b, π d} : Set (H →L[ℂ] H))) :
      ∀ x ∈ K.toSubmodule, T x ∈ K.toSubmodule :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1
      (hK T (StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hT)))
  let P := (reducingAlgebra K.toSubmodule).comap π
  have hPclosed : IsClosed (P : Set R) :=
    (reducingAlgebra_closed K.toSubmodule K.isClosed).preimage (map_continuous π)
  have hPgen : ({a, b, d} : Set R) ⊆ P := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht
    · subst t
      intro x hx
      have hax := K.toSubmodule.smul_mem (X : ℂ) (hmem ((X⁻¹ : ℝ) • π a) (by simp) x hx)
      have heq : X • ((X⁻¹ : ℝ) • π a) = π a := by rw [smul_smul, mul_inv_cancel₀ hX, one_smul]
      have hax' : π a x ∈ K.toSubmodule := by
        rw [Complex.coe_smul] at hax
        change (X • ((X⁻¹ : ℝ) • π a)) x ∈ K.toSubmodule at hax
        rw [heq] at hax
        exact hax
      change π a x ∈ K.toSubmodule ∧ (star (π a)) x ∈ K.toSubmodule
      rw [(ha.map π).star_eq]
      exact ⟨hax', hax'⟩
    · subst t
      intro x hx
      have hbx := K.toSubmodule.smul_mem (Y : ℂ) (hmem ((Y⁻¹ : ℝ) • π b) (by simp) x hx)
      have heq : Y • ((Y⁻¹ : ℝ) • π b) = π b := by rw [smul_smul, mul_inv_cancel₀ hY, one_smul]
      have hbx' : π b x ∈ K.toSubmodule := by
        rw [Complex.coe_smul] at hbx
        change (Y • ((Y⁻¹ : ℝ) • π b)) x ∈ K.toSubmodule at hbx
        rw [heq] at hbx
        exact hbx
      change π b x ∈ K.toSubmodule ∧ (star (π b)) x ∈ K.toSubmodule
      rw [(hb.map π).star_eq]
      exact ⟨hbx', hbx'⟩
    · subst t
      intro x hx
      have hdx := hmem (π d) (by simp) x hx
      change π d x ∈ K.toSubmodule ∧ (star (π d)) x ∈ K.toSubmodule
      rw [(hd.map π).star_eq]
      exact ⟨hdx, hdx⟩
  have hle := StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hPgen) hPclosed
  rw [hgen] at hle
  rintro T ⟨r, rfl⟩
  exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2
    (fun x hx => (hle (by trivial) x hx).1)

/-- Simultaneous coordinates of the actual triple in its closed generated C-star algebra.
Only the first two represented square parameters are restricted to the positive branch. -/
theorem positive_branch_coordinates {R : Type*} [CStarAlgebra R]
    (π : R →⋆ₐ[ℂ] (H →L[ℂ] H)) (a b d : R) (X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hd : IsSelfAdjoint d)
    (hab : a * b = -(b * a)) (had : a * d = -(d * a)) (hbd : b * d = -(d * b))
    (ha2 : π a * π a = (X ^ 2) • (1 : H →L[ℂ] H))
    (hb2 : π b * π b = (Y ^ 2) • (1 : H →L[ℂ] H))
    (hgen : (StarAlgebra.adjoin ℂ ({a, b, d} : Set R)).topologicalClosure = ⊤)
    (hirr : InnerProductSpace.IsTopologicallyIrreducible (Set.range π)) :
    ∃ (z : ℝ) (U : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2)),
      (∀ x, U (π a x) 0 = (X : ℂ) * U x 0 ∧ U (π a x) 1 = -(X : ℂ) * U x 1) ∧
      (∀ x, U (π b x) 0 = (Y : ℂ) * U x 1 ∧ U (π b x) 1 = (Y : ℂ) * U x 0) ∧
      (∀ x, U (π d x) 0 = -(Complex.I * (z : ℂ)) * U x 1 ∧
        U (π d x) 1 = (Complex.I * (z : ℂ)) * U x 0) := by
  let A := (X⁻¹ : ℝ) • π a
  let B := (Y⁻¹ : ℝ) • π b
  have hA : IsSelfAdjoint A := by
    change star A = A
    simp [A, star_smul, (ha.map π).star_eq]
  have hB : IsSelfAdjoint B := by
    change star B = B
    simp [B, star_smul, (hb.map π).star_eq]
  have hAA : A * A = 1 := by
    simp only [A, smul_mul_smul_comm, ha2, smul_smul]
    have : X⁻¹ * X⁻¹ * X ^ 2 = 1 := by field_simp [hX.ne']
    rw [this, one_smul]
  have hBB : B * B = 1 := by
    simp only [B, smul_mul_smul_comm, hb2, smul_smul]
    have : Y⁻¹ * Y⁻¹ * Y ^ 2 = 1 := by field_simp [hY.ne']
    rw [this, one_smul]
  have hpab : π a * π b = -(π b * π a) := by simpa using congrArg π hab
  have hpad : π a * π d = -(π d * π a) := by simpa using congrArg π had
  have hpbd : π b * π d = -(π d * π b) := by simpa using congrArg π hbd
  have hAB : A * B = -(B * A) := by
    simp only [A, B, smul_mul_smul_comm, hpab, smul_neg]
    rw [mul_comm (X⁻¹) (Y⁻¹)]
  have hAD : A * π d = -(π d * A) := by
    simp only [A, smul_mul_assoc, mul_smul_comm, hpad, smul_neg]
  have hBD : B * π d = -(π d * B) := by
    simp only [B, smul_mul_assoc, mul_smul_comm, hpbd, smul_neg]
  obtain ⟨z, U, hUa, hUb, hUd⟩ := exists_coordinates A B (π d) hA hB (hd.map π)
    hAA hBB hAB hAD hBD (normalized_irreducible π a b d X Y hX.ne' hY.ne'
      ha hb hd hgen hirr)
  have hea : π a = X • A := by simp [A, smul_smul, hX.ne']
  have heb : π b = Y • B := by simp [B, smul_smul, hY.ne']
  refine ⟨z, U, ?_, ?_, hUd⟩
  · intro x
    rw [hea, smul_apply, ← Complex.coe_smul, map_smul]
    constructor
    · change (X : ℂ) * U (A x) 0 = _
      rw [(hUa x).1]
    · change (X : ℂ) * U (A x) 1 = _
      rw [(hUa x).2, mul_neg, neg_mul]
  · intro x
    rw [heb, smul_apply, ← Complex.coe_smul, map_smul]
    constructor
    · change (Y : ℂ) * U (B x) 0 = _
      rw [(hUb x).1]
    · change (Y : ℂ) * U (B x) 1 = _
      rw [(hUb x).2]

end D5.S3.Quantum.Algebra.AnticommutingInvariantPlane
