/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Raw all-window actual-image recovery and individual marginal ambiguity. -/

import D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
import D5.S3.Analytic.Hunter.NCHunterPositivity

/-! Critch--Morton C9, raw actual-image reading. All auxiliary declarations serve result.
The candidate admission basis is open-problem-resolution, preregistered at issue #30422.
The conservative proof shape is bind-only. No normalization or physical dynamics is assumed.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30422. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9
open scoped BigOperators Matrix
open Matrix MvPolynomial
open PeriodicMPSParentIntersection (Word Bond wordMatrix)
open OpenBoundaryMPSMarginalBirationality (openBoundaryMPS mpsState)
open OpenBoundaryMPSDensityRecovery
open OpenBoundaryMPSDensityGenericity
open OpenBoundaryMPSIntrinsicQ2Fiber
open OpenBoundaryMPSInteriorGenericity
open OpenBoundaryMPSInteriorCommonCore (rawInterior interiorColumns)
open OpenBoundaryMPSQ2PolynomialFiber (ObsIndex actualPrincipalLocus)

private def rev {n : ℕ} (f : Word n → ℂ) : Word n → ℂ :=
  fun w => f (w ∘ Fin.rev)

private lemma rev_rev {n : ℕ} (f : Word n → ℂ) : rev (rev f) = f := by
  funext w
  simp [rev, Function.comp_def]

private lemma reverse_list {n : ℕ} (w : Word n) :
    List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse := by
  have hh := GVHunter.reverse_word_list w
  change List.ofFn (fun i => w (Fin.revPerm.symm i)) = _ at hh
  simpa only [Fin.revPerm_symm, Fin.revPerm_apply, Function.comp_def] using hh

private lemma mps_reverse (n : ℕ) (a b : Bond) (l r : Fin 2 → ℂ) :
    rev (mpsState n a b l r) = mpsState n aᵀ bᵀ r l := by
  have hw (A : Fin 2 → Bond) (w : Word n) :
      wordMatrix (fun i => (A i)ᵀ) (w ∘ Fin.rev) = (wordMatrix A w)ᵀ := by
    calc
      _ = (((List.ofFn w).reverse).map (fun i => (A i)ᵀ)).prod := by
        unfold wordMatrix
        rw [List.ofFn_comp' (w ∘ Fin.rev) (fun i => (A i)ᵀ), reverse_list]
      _ = (((List.ofFn w).map A).map Matrix.transpose).reverse.prod := by
        rw [List.map_reverse, List.map_map]
        rfl
      _ = _ := by
        simp only [wordMatrix, Matrix.transpose_list_prod, List.map_ofFn]
        rfl
  funext w
  let A : Fin 2 → Bond := ![a,b]
  have hAt : (fun i => (A i)ᵀ) = (![aᵀ,bᵀ] : Fin 2 → Bond) := by
    funext i; fin_cases i <;> rfl
  have hh := hw (fun i => (A i)ᵀ) w
  simp only [Matrix.transpose_transpose] at hh
  change dotProduct l (wordMatrix A (w ∘ Fin.rev) *ᵥ r) =
    dotProduct r (wordMatrix ![aᵀ,bᵀ] w *ᵥ l)
  rw [← hAt, hh]
  exact Matrix.dotProduct_transpose_mulVec _ _ _

private lemma rev_actual {n : ℕ} (f : openBoundaryMPS n) :
    rev (f : Word n → ℂ) ∈ openBoundaryMPS n := by
  obtain ⟨a,b,l,r,he⟩ := f.property
  exact ⟨aᵀ,bᵀ,r,l,by rw [he, mps_reverse]⟩

private def reverseHomeomorph (n : ℕ) : openBoundaryMPS n ≃ₜ openBoundaryMPS n where
  toFun f := ⟨rev f, rev_actual f⟩
  invFun f := ⟨rev f, rev_actual f⟩
  left_inv f := by apply Subtype.ext; exact rev_rev (f : Word n → ℂ)
  right_inv f := by apply Subtype.ext; exact rev_rev (f : Word n → ℂ)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro w
    exact (continuous_apply (w ∘ Fin.rev)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro w
    exact (continuous_apply (w ∘ Fin.rev)).comp continuous_subtype_val

private lemma rawInterior_prefix (k r : ℕ) (h : ((0 + k) + r) = k + r)
    (f : Word (k + r) → ℂ) :
    rawInterior 0 k r (castState h f) = rawPrefix k r f := by
  ext u v
  simp only [rawInterior, rawPrefix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    interiorColumns, amplitudeColumns, Fintype.sum_prod_type]
  have he (a : Word 0) (u : Word k) (b : Word r) :
      (fun i => Fin.append (Fin.append a u) b (Fin.cast h.symm i)) = Fin.append u b := by
    apply List.ofFn_injective
    rw [← List.ofFn_congr h, List.ofFn_fin_append, List.ofFn_fin_append]
    simp
  simp only [castState, he]
  simp

private lemma rawInterior_reverse (p k q : ℕ) (h : ((q + k) + p) = ((p + k) + q))
    (f : Word ((p + k) + q) → ℂ) (u v : Word k) :
    rawInterior p k q (rev f) u v =
      rawInterior q k p (castState h f) (u ∘ Fin.rev) (v ∘ Fin.rev) := by
  let rp : Word p ≃ Word p := Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))
  let rq : Word q ≃ Word q := Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))
  let e := (Equiv.prodComm (Word p) (Word q)).trans (Equiv.prodCongr rq rp)
  have he (a : Word p) (u : Word k) (b : Word q) :
      Fin.append (Fin.append a u) b ∘ Fin.rev =
        fun i => Fin.append (Fin.append (b ∘ Fin.rev) (u ∘ Fin.rev))
          (a ∘ Fin.rev) (Fin.cast h.symm i) := by
    apply List.ofFn_injective
    rw [reverse_list, ← List.ofFn_congr h]
    simp only [List.ofFn_fin_append, reverse_list, List.reverse_append, List.append_assoc]
  simp only [rawInterior, Matrix.mul_apply, Matrix.conjTranspose_apply, interiorColumns]
  apply Fintype.sum_equiv e
  intro ab
  simp only [rev, castState, he]
  rfl

private lemma rawPrefix_right (k r : ℕ) (h : ((r + k) + 0) = k + r)
    (f : Word (k + r) → ℂ) (u v : Word k) :
    rawPrefix k r (rev f) u v =
      rawInterior r k 0 (castState h f) (u ∘ Fin.rev) (v ∘ Fin.rev) := by
  have h0 : ((0 + k) + r) = k + r := by omega
  have hs : ((r + k) + 0) = ((0 + k) + r) := by omega
  rw [← rawInterior_prefix k r h0]
  have hh := rawInterior_reverse 0 k r hs (castState h0 f) u v
  have hc : castState hs (castState h0 f) = castState h f := by
    funext w
    apply congrArg f
    funext i
    exact congrArg w (Fin.ext rfl)
  rw [hc] at hh
  have hr : rev (castState h0 f) = castState h0 (rev f) := by
    funext w
    apply congrArg f
    funext i
    exact congrArg w (Fin.cast_rev i h0.symm).symm
  rw [hr] at hh
  exact hh

private lemma rawInterior_trace_last (p q : ℕ) (h : (p + 1) + (1 + q) = (p + 2) + q)
    (f : Word ((p + 2) + q) → ℂ) (i j : Fin 2) :
    (∑ b : Fin 2, rawInterior p 2 q f ![i,b] ![j,b]) =
      rawInterior p 1 (1 + q) (castState h f) (fun _ => i) (fun _ => j) := by
  let s : Word 1 ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
  let bq : (Fin 2 × Word q) ≃ Word (1 + q) :=
    (Equiv.prodCongr s.symm (Equiv.refl (Word q))).trans (Fin.appendEquiv 1 q)
  let t : (Fin 2 × (Word p × Word q)) ≃ ((Word p × Fin 2) × Word q) :=
    (Equiv.prodAssoc (Fin 2) (Word p) (Word q)).symm.trans
      (Equiv.prodCongr (Equiv.prodComm (Fin 2) (Word p)) (Equiv.refl (Word q)))
  let e := (t.trans (Equiv.prodAssoc (Word p) (Fin 2) (Word q))).trans
    (Equiv.prodCongr (Equiv.refl (Word p)) bq)
  have he (b : Fin 2) (a : Word p) (c : Word q) (i : Fin 2) :
      (fun z => Fin.append (Fin.append a (fun _ : Fin 1 => i))
        (Fin.append (fun _ : Fin 1 => b) c) (Fin.cast h.symm z)) =
          Fin.append (Fin.append a ![i,b]) c := by
    apply List.ofFn_injective
    rw [← List.ofFn_congr h]
    simp only [List.ofFn_fin_append]
    simp [List.ofFn_succ, List.append_assoc]
  simp only [rawInterior, Matrix.mul_apply, Matrix.conjTranspose_apply, interiorColumns]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv e
  rintro ⟨b,a,c⟩
  change _ =
    f (fun z => Fin.append (Fin.append a (fun _ : Fin 1 => i))
      (Fin.append (fun _ : Fin 1 => b) c) (Fin.cast h.symm z)) *
    star (f (fun z => Fin.append (Fin.append a (fun _ : Fin 1 => j))
      (Fin.append (fun _ : Fin 1 => b) c) (Fin.cast h.symm z)))
  rw [he,he]

private lemma rawInterior_trace_first (p q : ℕ) (h : ((p + 1) + 1) + q = (p + 2) + q)
    (f : Word ((p + 2) + q) → ℂ) (i j : Fin 2) :
    (∑ b : Fin 2, rawInterior p 2 q f ![b,i] ![b,j]) =
      rawInterior (p + 1) 1 q (castState h f) (fun _ => i) (fun _ => j) := by
  let s : Word 1 ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
  let pb : (Word p × Fin 2) ≃ Word (p + 1) :=
    (Equiv.prodCongr (Equiv.refl (Word p)) s.symm).trans (Fin.appendEquiv p 1)
  let t : (Fin 2 × (Word p × Word q)) ≃ ((Word p × Fin 2) × Word q) :=
    (Equiv.prodAssoc (Fin 2) (Word p) (Word q)).symm.trans
      (Equiv.prodCongr (Equiv.prodComm (Fin 2) (Word p)) (Equiv.refl (Word q)))
  let e := t.trans (Equiv.prodCongr pb (Equiv.refl (Word q)))
  have he (b : Fin 2) (a : Word p) (c : Word q) (i : Fin 2) :
      (fun z => Fin.append (Fin.append (Fin.append a (fun _ : Fin 1 => b))
        (fun _ : Fin 1 => i)) c (Fin.cast h.symm z)) =
          Fin.append (Fin.append a ![b,i]) c := by
    apply List.ofFn_injective
    rw [← List.ofFn_congr h]
    simp only [List.ofFn_fin_append]
    simp [List.ofFn_succ, List.append_assoc]
  simp only [rawInterior, Matrix.mul_apply, Matrix.conjTranspose_apply, interiorColumns]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv e
  rintro ⟨b,a,c⟩
  change _ =
    f (fun z => Fin.append (Fin.append (Fin.append a (fun _ : Fin 1 => b))
      (fun _ : Fin 1 => i)) c (Fin.cast h.symm z)) *
    star (f (fun z => Fin.append (Fin.append (Fin.append a (fun _ : Fin 1 => b))
      (fun _ : Fin 1 => j)) c (Fin.cast h.symm z)))
  rw [he,he]

private def q3Coordinates (m : ℕ) :
    ObsIndex ⊕ ObsIndex → MvPolynomial (Word (3 + m) ⊕ Word (3 + m)) ℝ :=
  Sum.elim
    (fun uv => ∑ b : Word m, (
      X (Sum.inl (Fin.append uv.1 b)) * X (Sum.inl (Fin.append uv.2 b)) +
      X (Sum.inr (Fin.append uv.1 b)) * X (Sum.inr (Fin.append uv.2 b))))
    (fun uv => ∑ b : Word m, (
      X (Sum.inr (Fin.append uv.1 b)) * X (Sum.inl (Fin.append uv.2 b)) -
      X (Sum.inl (Fin.append uv.1 b)) * X (Sum.inr (Fin.append uv.2 b))))

private def lift (m : ℕ) (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ) :
    MvPolynomial (Word (3 + m) ⊕ Word (3 + m)) ℝ := eval₂Hom C (q3Coordinates m) R

private lemma lift_eval (m : ℕ) (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ)
    (f : Word (3 + m) → ℂ) :
    eval (realCoordinates f) (lift m R) =
      eval (realCoordinates (fun uv : ObsIndex => rawPrefix 3 m f uv.1 uv.2)) R := by
  have he : (eval (realCoordinates f) ∘ q3Coordinates m) =
      realCoordinates (fun uv : ObsIndex => rawPrefix 3 m f uv.1 uv.2) := by
    funext uv
    cases uv <;>
      simp [q3Coordinates, realCoordinates, rawPrefix, amplitudeColumns,
        mul_apply, conjTranspose_apply, Complex.mul_re, Complex.mul_im,
        sub_eq_add_neg, add_comm]
  change eval (realCoordinates f) (eval₂ C (q3Coordinates m) R) = _
  rw [← eval_assoc, he]

private lemma rename_reverse_eval (m : ℕ)
    (F : MvPolynomial (Word (3 + m) ⊕ Word (3 + m)) ℝ) (f : Word (3 + m) → ℂ) :
    eval (realCoordinates f)
        (rename (Sum.map (fun w => w ∘ Fin.rev) (fun w => w ∘ Fin.rev)) F) =
      eval (realCoordinates (rev f)) F := by
  rw [eval_rename]
  apply congrArg (fun x => eval x F)
  funext i
  cases i <;> rfl

private lemma left_observation (k r n : ℕ) (e : k + r = n)
    (h : ((0 + k) + r) = n) (f : Word n → ℂ) :
    rawInterior 0 k r (castState h f) = rawPrefix k r (castState e f) := by
  subst n
  exact rawInterior_prefix k r h f

private lemma right_observation (k r n : ℕ) (e : k + r = n)
    (h : ((r + k) + 0) = n) (f : Word n → ℂ) (u v : Word k) :
    rawPrefix k r (castState e (rev f)) u v =
      rawInterior r k 0 (castState h f) (u ∘ Fin.rev) (v ∘ Fin.rev) := by
  subst n
  exact rawPrefix_right k r h f u v

private lemma right_equal_iff (k r n : ℕ) (e : k + r = n)
    (h : ((r + k) + 0) = n) (f g : Word n → ℂ) :
    rawInterior r k 0 (castState h f) = rawInterior r k 0 (castState h g) ↔
      rawPrefix k r (castState e (rev f)) = rawPrefix k r (castState e (rev g)) := by
  constructor
  · intro he
    ext u v
    rw [right_observation k r n e h, right_observation k r n e h, he]
  · intro he
    ext u v
    have hh := congrFun (congrFun he (u ∘ Fin.rev)) (v ∘ Fin.rev)
    rw [right_observation k r n e h, right_observation k r n e h] at hh
    simpa only [Function.comp_def, Fin.rev_rev] using hh

private lemma good_nonzero (m : ℕ) (f : openBoundaryMPS (3 + m))
    (hf : f ∈ goodStates m) : (f : Word (3 + m) → ℂ) ≠ 0 := by
  change eval (realCoordinates (fun ij : ObsIndex => rawPrefix 3 m
    (f : Word (3 + m) → ℂ) ij.1 ij.2)) observedPolynomial ≠ 0 at hf
  have hg := (recoveryPolynomial_ne_zero _).mp
    (observedPolynomial_eval (rawPrefix 3 m f) ▸ hf)
  intro hz
  have ht : fixedTensor (rawPrefix 3 m (f : Word (3 + m) → ℂ)) = 0 := by
    rw [hz]
    ext u
    simp [fixedTensor, rawPrefix, amplitudeColumns, Matrix.mul_apply]
  rw [ht] at hg
  apply hg.1
  simp [OpenBoundaryMPSMarginalBirationality.chartPoly,
    OpenBoundaryMPSMarginalBirationality.coordinate]


private lemma one_site_of_pairs (m : ℕ) (ψ : openBoundaryMPS (3 + m))
    (hpairs : ∀ p q : ℕ, p + q = m + 1 → ∀ h : ((p + 2) + q) = 3 + m,
      ∃ φ : openBoundaryMPS (3 + m), (φ : Word (3 + m) → ℂ) ≠ 0 ∧
        rawInterior p 2 q (castState h φ) = rawInterior p 2 q (castState h ψ) ∧
        ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)) :
    ∀ p q : ℕ, p + q = m + 2 → ∀ h : ((p + 1) + q) = 3 + m,
      ∃ φ : openBoundaryMPS (3 + m), (φ : Word (3 + m) → ℂ) ≠ 0 ∧
        rawInterior p 1 q (castState h φ) = rawInterior p 1 q (castState h ψ) ∧
        ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ) := by
  intro p q hpq h
  by_cases hq : q = 0
  · subst q
    obtain ⟨r, rfl⟩ : ∃ r : ℕ, p = r + 1 := ⟨p - 1, by omega⟩
    have e : ((r + 2) + 0) = 3 + m := by omega
    obtain ⟨φ,hne,hraw,hnon⟩ := hpairs r 0 (by omega) e
    refine ⟨φ,hne,?_,hnon⟩
    have ht : ((r + 1) + 1) + 0 = (r + 2) + 0 := by omega
    have hc (f : Word (3 + m) → ℂ) : castState ht (castState e f) = castState h f := by
      funext w
      apply congrArg f
      funext i
      exact congrArg w (Fin.ext rfl)
    ext u v
    have hh := congrArg (fun Q : Matrix (Word 2) (Word 2) ℂ =>
      ∑ b : Fin 2, Q ![b,u 0] ![b,v 0]) hraw
    rw [rawInterior_trace_first r 0 ht, rawInterior_trace_first r 0 ht, hc, hc] at hh
    have hu : (fun _ : Fin 1 => u 0) = u := funext (fun i => congrArg u (Subsingleton.elim 0 i))
    have hv : (fun _ : Fin 1 => v 0) = v := funext (fun i => congrArg v (Subsingleton.elim 0 i))
    simpa only [hu,hv] using hh
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = 1 + r := ⟨q - 1, by omega⟩
    have e : ((p + 2) + r) = 3 + m := by omega
    obtain ⟨φ,hne,hraw,hnon⟩ := hpairs p r (by omega) e
    refine ⟨φ,hne,?_,hnon⟩
    have ht : (p + 1) + (1 + r) = (p + 2) + r := by omega
    have hc (f : Word (3 + m) → ℂ) : castState ht (castState e f) = castState h f := by
      funext w
      apply congrArg f
      funext i
      exact congrArg w (Fin.ext rfl)
    ext u v
    have hh := congrArg (fun Q : Matrix (Word 2) (Word 2) ℂ =>
      ∑ b : Fin 2, Q ![u 0,b] ![v 0,b]) hraw
    rw [rawInterior_trace_last p r ht, rawInterior_trace_last p r ht, hc, hc] at hh
    have hu : (fun _ : Fin 1 => u 0) = u := funext (fun i => congrArg u (Subsingleton.elim 0 i))
    have hv : (fun _ : Fin 1 => v 0) = v := funext (fun i => congrArg v (Subsingleton.elim 0 i))
    simpa only [hu,hv] using hh

set_option maxHeartbeats 2400000 in
/-- Raw all-window recovery and sharp individual one/two-site ambiguity on one full-state
principal real-polynomial locus in the entire actual binary bond-two open-boundary image. -/
theorem result (m : ℕ) :
    ∃ P : MvPolynomial ((Word (3 + m)) ⊕ (Word (3 + m))) ℝ,
      P ≠ 0 ∧
      let G : Set (openBoundaryMPS (3 + m)) :=
        {ψ | eval (realCoordinates (ψ : Word (3 + m) → ℂ)) P ≠ 0}
      G.Nonempty ∧ IsOpen G ∧ Dense G ∧
      (∀ (ψ : openBoundaryMPS (3 + m)) (z : ℂ), ‖z‖ = 1 →
        ∃ hz : z • (ψ : Word (3 + m) → ℂ) ∈ openBoundaryMPS (3 + m),
          (⟨z • (ψ : Word (3 + m) → ℂ), hz⟩ ∈ G ↔ ψ ∈ G)) ∧
      ∀ ψ : openBoundaryMPS (3 + m), ψ ∈ G →
        (ψ : Word (3 + m) → ℂ) ≠ 0 ∧
        (∀ p q : ℕ, p + q = m →
          ∀ h : ((p + 3) + q) = 3 + m,
          ∀ φ : openBoundaryMPS (3 + m),
            rawInterior p 3 q (castState h (φ : Word (3 + m) → ℂ)) =
              rawInterior p 3 q (castState h (ψ : Word (3 + m) → ℂ)) ↔
            ∃ z : ℂ, ‖z‖ = 1 ∧
              (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)) ∧
        (∀ p q : ℕ, p + q = m + 1 →
          ∀ h : ((p + 2) + q) = 3 + m,
            ∃ φ : openBoundaryMPS (3 + m),
              (φ : Word (3 + m) → ℂ) ≠ 0 ∧
              rawInterior p 2 q (castState h (φ : Word (3 + m) → ℂ)) =
                rawInterior p 2 q (castState h (ψ : Word (3 + m) → ℂ)) ∧
              ¬ ∃ z : ℂ, ‖z‖ = 1 ∧
                (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)) ∧
        (∀ p q : ℕ, p + q = m + 2 →
          ∀ h : ((p + 1) + q) = 3 + m,
            ∃ φ : openBoundaryMPS (3 + m),
              (φ : Word (3 + m) → ℂ) ≠ 0 ∧
              rawInterior p 1 q (castState h (φ : Word (3 + m) → ℂ)) =
                rawInterior p 1 q (castState h (ψ : Word (3 + m) → ℂ)) ∧
              ¬ ∃ z : ℂ, ‖z‖ = 1 ∧
                (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)) := by
  obtain ⟨hOn,hOo,hOd,hOr⟩ := intrinsic_recovery_genericity m
  obtain ⟨B,hB,hBn,hBo,hBd,hBr⟩ := intrinsic_actual_q2_fiber m
  obtain ⟨T,hTo,hTd,hTr⟩ : ∃ T : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ,
      IsOpen (actualPrincipalLocus m T) ∧ Dense (actualPrincipalLocus m T) ∧
      (∀ hm : 2 ≤ m, ∀ ψ : openBoundaryMPS (3 + m), ψ ∈ actualPrincipalLocus m T →
        ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → p + q = m →
        ∀ h : ((p + 3) + q) = 3 + m, ∀ φ : openBoundaryMPS (3 + m),
          rawInterior p 3 q (castState h φ) = rawInterior p 3 q (castState h ψ) ↔
          ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)) := by
    by_cases hm : 2 ≤ m
    · obtain ⟨T,_,_,ho,hd,_,hr⟩ := intrinsic_interior_recovery m hm
      exact ⟨T,ho,hd,fun _ ψ hψ => (hr ψ hψ).2.2.2.2.2⟩
    · refine ⟨1,?_,?_,?_⟩
      · simp [actualPrincipalLocus]
      · simp [actualPrincipalLocus]
      · intro hm'; omega
  obtain ⟨A,hAo,hAd,hAr⟩ : ∃ A : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ,
      IsOpen (actualPrincipalLocus m A) ∧ Dense (actualPrincipalLocus m A) ∧
      (∀ hm : 1 ≤ m, ∀ ψ : openBoundaryMPS (3 + m), ψ ∈ actualPrincipalLocus m A →
        ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → p + q = m + 1 →
        ∀ h : ((p + 2) + q) = 3 + m,
          ∃ φ : openBoundaryMPS (3 + m), (φ : Word (3 + m) → ℂ) ≠ 0 ∧
            rawInterior p 2 q (castState h φ) = rawInterior p 2 q (castState h ψ) ∧
            ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ)) := by
    by_cases hm : 1 ≤ m
    · obtain ⟨A,_,_,ho,hd,_,hr⟩ := InteriorSpectralAmbiguity.observed_interior_ambiguity m hm
      exact ⟨A,ho,hd,fun _ => hr⟩
    · refine ⟨1,?_,?_,?_⟩
      · simp [actualPrincipalLocus]
      · simp [actualPrincipalLocus]
      · intro hm'; omega
  have hprod (R S : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ) :
      actualPrincipalLocus m (R * S) = actualPrincipalLocus m R ∩ actualPrincipalLocus m S := by
    ext ψ
    simp [actualPrincipalLocus]
  let L := observedPolynomial * B * T * A
  let R := observedPolynomial * B
  let H := reverseHomeomorph (3 + m)
  let E := actualPrincipalLocus m L ∩ H ⁻¹' (actualPrincipalLocus m R)
  have hLO : IsOpen (actualPrincipalLocus m L) := by
    dsimp [L]
    rw [hprod,hprod,hprod]
    exact ((hOo.inter hBo).inter hTo).inter hAo
  have hLD : Dense (actualPrincipalLocus m L) := by
    dsimp [L]
    rw [hprod,hprod,hprod]
    exact ((hOd.inter_of_isOpen_right hBd hBo).inter_of_isOpen_right hTd hTo).inter_of_isOpen_right hAd hAo
  have hRO : IsOpen (actualPrincipalLocus m R) := by
    dsimp [R]; rw [hprod]; exact hOo.inter hBo
  have hRD : Dense (actualPrincipalLocus m R) := by
    dsimp [R]; rw [hprod]; exact hOd.inter_of_isOpen_right hBd hBo
  have hEO : IsOpen E := hLO.inter (hRO.preimage H.continuous)
  have hED : Dense E := hLD.inter_of_isOpen_right
    (H.isOpenQuotientMap.dense_preimage_iff.mpr hRD) (hRO.preimage H.continuous)
  obtain ⟨ψstar,_,hstar⟩ := hED.inter_open_nonempty Set.univ isOpen_univ
    ⟨hOn.choose,Set.mem_univ _⟩
  let P := lift m L * rename (Sum.map (fun w => w ∘ Fin.rev) (fun w => w ∘ Fin.rev)) (lift m R)
  have hPE (ψ : openBoundaryMPS (3 + m)) :
      eval (realCoordinates (ψ : Word (3 + m) → ℂ)) P ≠ 0 ↔ ψ ∈ E := by
    simp only [P,map_mul,mul_ne_zero_iff,rename_reverse_eval,lift_eval]
    rfl
  have hP : P ≠ 0 := by
    intro hz
    have hh := (hPE ψstar).mpr hstar
    simp [hz] at hh
  have hGE : {ψ : openBoundaryMPS (3 + m) | eval (realCoordinates (ψ : Word (3 + m) → ℂ)) P ≠ 0} = E :=
    Set.ext hPE
  have hparts (ψ : openBoundaryMPS (3 + m)) (hψ : ψ ∈ E) :
      (((ψ ∈ goodStates m ∧ ψ ∈ actualPrincipalLocus m B) ∧ ψ ∈ actualPrincipalLocus m T) ∧
        ψ ∈ actualPrincipalLocus m A) ∧ (H ψ ∈ goodStates m ∧ H ψ ∈ actualPrincipalLocus m B) := by
    simpa only [E,L,R,hprod,Set.mem_inter_iff,Set.mem_preimage,
      goodStates,actualPrincipalLocus,Set.mem_ofPred_eq,map_mul,mul_ne_zero_iff] using hψ
  have hleft (ψ : openBoundaryMPS (3 + m)) (hψ : ψ ∈ actualPrincipalLocus m B)
      (hne : (ψ : Word (3 + m) → ℂ) ≠ 0) :
      ∃ φ : openBoundaryMPS (3 + m), (φ : Word (3 + m) → ℂ) ≠ 0 ∧
        rawPrefix 2 (1 + m) (castState (by omega : 2 + (1 + m) = 3 + m) (φ : Word (3 + m) → ℂ)) =
          rawPrefix 2 (1 + m) (castState (by omega : 2 + (1 + m) = 3 + m) (ψ : Word (3 + m) → ℂ)) ∧
        ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ) := by
    let V : Set (openBoundaryMPS (3 + m)) := {φ | (φ : Word (3 + m) → ℂ) ≠ 0}
    have hVo : IsOpen V := isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
    obtain ⟨φ,hφ,hraw,hnon⟩ := hBr ψ hψ V (hVo.mem_nhds hne)
    refine ⟨φ,hφ,?_,hnon⟩
    change rawPrefix 2 (1 + m) (castState (by omega : 2 + (1 + m) = 3 + m) (φ : Word (3 + m) → ℂ)) =
      rawPrefix 2 (1 + m) (castState (by omega : 2 + (1 + m) = 3 + m) (ψ : Word (3 + m) → ℂ)) at hraw
    exact hraw
  refine ⟨P,hP,?_⟩
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [hGE]
  refine ⟨⟨ψstar,hstar⟩,hEO,hED,?_,?_⟩
  · intro ψ z hz
    refine ⟨actual_phase _ ψ z,?_⟩
    have hl := locus_phase m L ψ z hz
    have hr := locus_phase m R (H ψ) z hz
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_congr hl hr
  · intro ψ hψ
    obtain ⟨⟨⟨⟨hO,hBψ⟩,hTψ⟩,hAψ⟩,hOrev,hBrev⟩ := hparts ψ hψ
    have hne := good_nonzero m ψ hO
    have hpairs : ∀ p q : ℕ, p + q = m + 1 → ∀ h : ((p + 2) + q) = 3 + m,
        ∃ φ : openBoundaryMPS (3 + m), (φ : Word (3 + m) → ℂ) ≠ 0 ∧
          rawInterior p 2 q (castState h φ) = rawInterior p 2 q (castState h ψ) ∧
          ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word (3 + m) → ℂ) = z • (ψ : Word (3 + m) → ℂ) := by
      intro p q hpq h
      by_cases hp : p = 0
      · subst p
        have hq : q = 1 + m := by omega
        subst q
        obtain ⟨φ,hφ,hraw,hnon⟩ := hleft ψ hBψ hne
        refine ⟨φ,hφ,?_,hnon⟩
        rwa [left_observation 2 (1 + m) (3 + m) (by omega) h,
          left_observation 2 (1 + m) (3 + m) (by omega) h]
      · by_cases hq : q = 0
        · subst q
          have hp' : p = 1 + m := by omega
          subst p
          obtain ⟨χ,hχ,hraw,hnon⟩ := hleft (H ψ) hBrev (good_nonzero m (H ψ) hOrev)
          refine ⟨H χ,?_,?_,?_⟩
          · intro hz
            have hh := congrArg rev hz
            change rev (rev (χ : Word (3 + m) → ℂ)) = rev 0 at hh
            apply hχ
            rw [rev_rev] at hh
            exact hh.trans (show rev (0 : Word (3 + m) → ℂ) = 0 from rfl)
          · apply (right_equal_iff 2 (1 + m) (3 + m) (by omega) h _ _).mpr
            change rawPrefix 2 (1 + m) (castState (by omega : 2 + (1 + m) = 3 + m) (rev (rev (χ : Word (3 + m) → ℂ)))) = _
            rwa [rev_rev]
          · rintro ⟨z,hz,heq⟩
            apply hnon
            refine ⟨z,hz,?_⟩
            have hh := congrArg rev heq
            change rev (rev (χ : Word (3 + m) → ℂ)) = z • rev (ψ : Word (3 + m) → ℂ) at hh
            rwa [rev_rev] at hh
        · exact hAr (by omega) ψ hAψ p q (by omega) (by omega) hpq h
    refine ⟨hne,?_,hpairs,one_site_of_pairs m ψ hpairs⟩
    intro p q hpq h φ
    constructor
    · intro hraw
      by_cases hp : p = 0
      · subst p
        have hq : q = m := by omega
        subst q
        apply (hOr ψ hO φ φ.property).mp
        rw [left_observation 3 m (3 + m) rfl h,
          left_observation 3 m (3 + m) rfl h] at hraw
        exact hraw
      · by_cases hq : q = 0
        · subst q
          have hp' : p = m := by omega
          subst p
          have hr := (right_equal_iff 3 m (3 + m) rfl h φ ψ).mp hraw
          obtain ⟨z,hz,heq⟩ := (hOr (H ψ) hOrev (rev (φ : Word (3 + m) → ℂ)) (rev_actual φ)).mp hr
          refine ⟨z,hz,?_⟩
          have hh := congrArg rev heq
          change rev (rev (φ : Word (3 + m) → ℂ)) = z • rev (rev (ψ : Word (3 + m) → ℂ)) at hh
          simpa only [rev_rev] using hh
        · exact (hTr (by omega) ψ hTψ p q (by omega) (by omega) hpq h φ).mp hraw
    · rintro ⟨z,hz,heq⟩
      rw [heq]
      exact rawInterior_phase p 3 q (castState h ψ) z hz

#print axioms result

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9
