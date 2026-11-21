/- GID: D5/S3/Quantum/Foundation/TripleMatrixRecords
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TripleMatrixRecords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent coordinates give pair discard and six record relabelings. -/

import D5.S3.Quantum.Foundation.PositiveMarginalMatrixTriple
import D5.S3.Quantum.Foundation.TripleMatrixOrientation

/-!
# Coherent coordinates, discard and relabeling for the actual matrix triple

The pair and triple coordinates act on the carriers of the supplied
preparations. The record permutations are conjugates of the ordinary
factor permutations, and the pair marginals are transported partial traces.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace PositiveMarginalMatrixComposition.TripleOrientation

variable {n : ℕ}
variable {M : H n →ₗ[ℝ] H n →ₗ[ℝ] H (n * n)}
variable {L : H (n * n) →ₗ[ℝ] H n →ₗ[ℝ] H (TripleSize n)}
variable {U : ↥(unitary (Mat (n * n)))} {V : ↥(unitary (Mat (TripleSize n)))}
variable {ε δ α β : Bool}

/-- The two changes of coordinates in (29)–(30), with the singleton
coordinates left at the identity. -/
structure CoherentCoordinates
    (M : H n →ₗ[ℝ] H n →ₗ[ℝ] H (n * n))
    (L : H (n * n) →ₗ[ℝ] H n →ₗ[ℝ] H (TripleSize n)) where
  pair : H (n * n) ≃ₗ[ℝ] H (n * n)
  triple : H (TripleSize n) ≃ₗ[ℝ] H (TripleSize n)
  pair_psd : ∀ q, (pair q).val.PosSemidef ↔ q.val.PosSemidef
  triple_psd : ∀ w, (triple w).val.PosSemidef ↔ w.val.PosSemidef
  pair_tp : ∀ q, tr (pair q) = tr q
  triple_tp : ∀ w, tr (triple w) = tr w
  prep_pair : ∀ x y, pair (M x y) = tensor x y
  prep_triple : ∀ q z, triple (L q z) = tensor (pair q) z

private def tensorRight {m k : ℕ} (z : H k) : H m →ₗ[ℝ] H (m * k) where
  toFun q := tensor q z
  map_add' x y := Subtype.ext (congrArg pack (Matrix.add_kronecker x.val y.val z.val))
  map_smul' c x := Subtype.ext (congrArg pack (Matrix.smul_kronecker c x.val z.val))

private theorem transposeH_subsingleton {m : ℕ} [Subsingleton (Fin m)] (b : Bool) (x : H m) :
    transposeH b x = x := by
  cases b
  · rfl
  · apply Subtype.ext
    ext i j
    change x.val j i = x.val i j
    rw [Subsingleton.elim j i]

private def coordinatesOfCommonBits
    (hm : TensorNormalForm M U ε δ) (hl : TensorNormalForm L V α β) (hM : Spans M)
    (hp : ε = δ) (h1 : (α ^^ ε) = β) (h2 : (α ^^ δ) = β) :
    CoherentCoordinates M L := by
  let pair := (adjH U).symm.trans (transposeH ε)
  let triple := (tripleFrame U V α).symm.trans (transposeH β)
  have pairPrep (x y : H n) : pair (M x y) = tensor x y := by
    have hb : (ε ^^ ε) = false := by cases ε <;> rfl
    rw [hm x y]
    simp only [pair, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, tensor_transposeH,
      transposeH_xor, ← hp, hb, transposeH_false]
  refine ⟨pair, triple, ?_, ?_, ?_, ?_, pairPrep, ?_⟩
  · intro q
    have h := adjH_psd U ((adjH U).symm q)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (transposeH_psd ε _).trans h.symm
  · intro w
    have h := tripleFrame_psd U V α ((tripleFrame U V α).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (transposeH_psd β _).trans h.symm
  · intro q
    have h := adjH_tp U ((adjH U).symm q)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (transposeH_tp ε _).trans h.symm
  · intro w
    have h := tripleFrame_tp U V α ((tripleFrame U V α).symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (transposeH_tp β _).trans h.symm
  · intro q z
    let F := triple.toLinearMap.comp (L.flip z)
    let G := (tensorRight z).comp pair.toLinearMap
    have heq : F - G = 0 := by
      apply eq_of_products hM
      intro x y
      apply sub_eq_zero.mpr
      change triple (L (M x y) z) = tensor (pair (M x y)) z
      have hb : (β ^^ β) = false := by cases β <;> rfl
      rw [pairPrep, triple_normal hm hl x y z, h1, h2]
      simp only [triple, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        tensor_transposeH, transposeH_xor, hb, transposeH_false]
    exact sub_eq_zero.mp (LinearMap.congr_fun heq q)

/-- Positive readback for the two overlapping pairs gives (30) on every
pair vector, including entangled inputs. Scalar transposes act trivially. -/
def coherentCoordinates (hn : 0 < n)
    (hm : TensorNormalForm M U ε δ) (hl : TensorNormalForm L V α β)
    (hM : Spans M) (hL : Spans L)
    (p13 p23 : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (pos13 : ∀ w, w.val.PosSemidef → (p13 w).val.PosSemidef)
    (pos23 : ∀ w, w.val.PosSemidef → (p23 w).val.PosSemidef)
    (read13 : ∀ x y z, p13 (L (M x y) z) = tr y • M x z)
    (read23 : ∀ x y z, p23 (L (M x y) z) = tr x • M y z) :
    CoherentCoordinates M L := by
  by_cases h : 2 ≤ n
  · obtain ⟨_, _, _, hEq, h1, h2⟩ :=
      align_bits h hm hl hM hL p13 p23 pos13 pos23 read13 read23
    have hp : ε = δ := by cases ε <;> cases δ <;> first | contradiction | rfl
    exact coordinatesOfCommonBits hm hl hM hp h1 h2
  · obtain rfl : n = 1 := by omega
    have hm' : TensorNormalForm M U false false := by
      intro x y
      simpa only [transposeH_subsingleton] using hm x y
    have hl' : TensorNormalForm L V false false := by
      intro q z
      have hq (b : Bool) : transposeH b q = q :=
        transposeH_subsingleton (m := 1) b q
      simpa only [hq, transposeH_subsingleton] using hl q z
    exact coordinatesOfCommonBits hm' hl' hM rfl rfl rfl

/-- Apply the orientation theorem to the three-copy data used by
`triple_recover`. -/
def coherentCoordinatesOfTriple (hn : 0 < n)
    (hm : TensorNormalForm M U ε δ) (hl : TensorNormalForm L V α β)
    (hM : Spans M) (hL : Spans L)
    {r : H (n * n) →ₗ[ℝ] H n} {p12 p13 p23 : H (TripleSize n) →ₗ[ℝ] H (n * n)}
    (h : TripleMarginals M L r p12 p13 p23) : CoherentCoordinates M L :=
  coherentCoordinates hn hm hl hM hL p13 p23 h.pos13 h.pos23 h.read13 h.read23

namespace CoherentCoordinates

variable (C : CoherentCoordinates M L)

/-- Trace out the last factor on the actual triple and return to the actual pair. -/
def marginal12 : H (TripleSize n) →ₗ[ℝ] H (n * n) :=
  C.pair.symm.toLinearMap.comp (traceLast.comp C.triple.toLinearMap)

theorem marginal12_psd (w : H (TripleSize n)) (hw : w.val.PosSemidef) :
    (C.marginal12 w).val.PosSemidef := by
  apply (C.pair_psd _).mp
  simpa only [marginal12, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using traceLast_psd ((C.triple_psd w).mpr hw)

theorem marginal12_tp (w : H (TripleSize n)) : tr (C.marginal12 w) = tr w := by
  rw [← C.pair_tp (C.marginal12 w)]
  simp only [marginal12, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, traceLast_tp, C.triple_tp]

theorem marginal12_read (q : H (n * n)) (z : H n) :
    C.marginal12 (L q z) = tr z • q := by
  simp only [marginal12, LinearMap.comp_apply, LinearEquiv.coe_coe, C.prep_triple,
    traceLast_tensor, map_smul, LinearEquiv.symm_apply_apply]

theorem marginal12_unique (hL : Spans L) (p : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (hp : ∀ q z, p (L q z) = tr z • q) : p = C.marginal12 := by
  apply sub_eq_zero.mp
  apply eq_of_products hL
  intro q z
  exact sub_eq_zero.mpr ((hp q z).trans (C.marginal12_read q z).symm)

/-- Relabel the three records by permuting tensor factors in coherent coordinates. -/
def recordRelabel (σ : Equiv.Perm (Fin 3)) : H (TripleSize n) ≃ₗ[ℝ] H (TripleSize n) :=
  C.triple.trans ((permute σ).trans C.triple.symm)

theorem recordRelabel_psd (σ : Equiv.Perm (Fin 3)) (w : H (TripleSize n)) :
    (C.recordRelabel σ w).val.PosSemidef ↔ w.val.PosSemidef := by
  rw [← C.triple_psd (C.recordRelabel σ w)]
  simpa only [recordRelabel, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    permute_psd] using C.triple_psd w

theorem recordRelabel_tp (σ : Equiv.Perm (Fin 3)) (w : H (TripleSize n)) :
    tr (C.recordRelabel σ w) = tr w := by
  rw [← C.triple_tp (C.recordRelabel σ w), ← C.triple_tp w]
  change tr (C.triple (C.triple.symm (permute σ (C.triple w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  unfold tr
  congr 1
  exact Equiv.sum_comp (slotPerm (n := n) σ) (fun i => (C.triple w).val i i)

/-- In an active sector, the six label permutations are distinct trace-preserving
PSD order automorphisms of the actual triple. -/
theorem recordRelabel_faithful (hn : 2 ≤ n) :
    Function.Injective C.recordRelabel ∧
      ∀ σ w, ((C.recordRelabel σ w).val.PosSemidef ↔ w.val.PosSemidef) ∧
        tr (C.recordRelabel σ w) = tr w := by
  refine ⟨?_, fun σ w => ⟨C.recordRelabel_psd σ w, C.recordRelabel_tp σ w⟩⟩
  intro σ τ he
  have hre (q : H (TripleSize n)) : permute σ q = permute τ q := by
    have hw := congrArg
      (fun P : H (TripleSize n) ≃ₗ[ℝ] H (TripleSize n) => C.triple (P (C.triple.symm q))) he
    simpa only [recordRelabel, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using hw
  have hslots (k : Fin (TripleSize n)) : slotPerm σ k = slotPerm τ k := by
    by_contra hne
    let diag (i : Fin (TripleSize n)) : ℂ := if i = slotPerm σ k then 1 else 0
    let q : H (TripleSize n) := ⟨Matrix.diagonal diag,
      Matrix.isHermitian_diagonal_of_self_adjoint diag (by
        change star diag = diag
        funext i
        change star (diag i) = diag i
        by_cases hi : i = slotPerm σ k <;> simp [diag, hi])⟩
    have hk := congrArg (fun x : H (TripleSize n) => x.val k k) (hre q)
    change (Matrix.diagonal diag) (slotPerm σ k) (slotPerm σ k) =
      (Matrix.diagonal diag) (slotPerm τ k) (slotPerm τ k) at hk
    simp [diag, Ne.symm hne] at hk
  have hs : σ.symm = τ.symm := by
    apply Equiv.ext
    intro i
    by_contra hi
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hval := congrArg Fin.val h
      simp [a, b] at hval
    let f (j : Fin 3) := if j = σ.symm i then a else b
    let k := (slots n).symm f
    have hslot (ρ : Equiv.Perm (Fin 3)) : slots n (slotPerm ρ k) i = f (ρ.symm i) := by
      simp [slotPerm, Equiv.arrowCongr, k]
    have hh := congrArg (fun j => slots n j i) (hslots k)
    change slots n (slotPerm σ k) i = slots n (slotPerm τ k) i at hh
    rw [hslot σ, hslot τ] at hh
    exact hab (by simpa [f, Ne.symm hi] using hh)
  exact congrArg Equiv.symm hs

theorem recordRelabel_prep (σ : Equiv.Perm (Fin 3)) (f : Fin 3 → H n) :
    C.recordRelabel σ (L (M (f 0) (f 1)) (f 2)) =
      L (M (f (σ 0)) (f (σ 1))) (f (σ 2)) := by
  apply C.triple.injective
  simp only [recordRelabel, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    C.prep_triple, C.prep_pair]
  exact permute_tensor σ f

theorem recordRelabel_comp (hM : Spans M) (hL : Spans L) (σ τ : Equiv.Perm (Fin 3)) :
    (C.recordRelabel σ).trans (C.recordRelabel τ) = C.recordRelabel (τ.trans σ) := by
  apply LinearEquiv.toLinearMap_injective
  apply eq_on_nested hM hL
  intro x y z
  let f : Fin 3 → H n := ![x,y,z]
  change C.recordRelabel τ (C.recordRelabel σ (L (M (f 0) (f 1)) (f 2))) =
    C.recordRelabel (τ.trans σ) (L (M (f 0) (f 1)) (f 2))
  rw [C.recordRelabel_prep σ f, C.recordRelabel_prep (τ.trans σ) f]
  exact C.recordRelabel_prep τ (f ∘ σ)

/-- Every actual retained-pair readback is the corresponding permutation
followed by the constructed first-pair discard. -/
theorem retained_eq_marginal12_relabel (hM : Spans M) (hL : Spans L)
    (σ : Equiv.Perm (Fin 3)) (p : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (hp : ∀ f : Fin 3 → H n, p (L (M (f 0) (f 1)) (f 2)) =
      tr (f (σ 2)) • M (f (σ 0)) (f (σ 1))) :
    p = C.marginal12.comp (C.recordRelabel σ).toLinearMap := by
  apply eq_on_nested hM hL
  intro x y z
  let f : Fin 3 → H n := ![x,y,z]
  change p (L (M (f 0) (f 1)) (f 2)) =
    C.marginal12 (C.recordRelabel σ (L (M (f 0) (f 1)) (f 2)))
  rw [hp, C.recordRelabel_prep, C.marginal12_read]

/-- The all-vector retained readback alone determines a positive trace-preserving map
once the actual preparations have coherent coordinates. -/
theorem retained_pair_psd_tp (C : CoherentCoordinates M L) (hM : Spans M) (hL : Spans L)
    (σ : Equiv.Perm (Fin 3)) (p : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (hp : ∀ f : Fin 3 → H n, p (L (M (f 0) (f 1)) (f 2)) =
      tr (f (σ 2)) • M (f (σ 0)) (f (σ 1))) :
    (∀ w, w.val.PosSemidef → (p w).val.PosSemidef) ∧ (∀ w, tr (p w) = tr w) := by
  rw [C.retained_eq_marginal12_relabel hM hL σ p hp]
  exact ⟨fun w hw => C.marginal12_psd _ ((C.recordRelabel_psd σ w).mpr hw),
    fun w => (C.marginal12_tp _).trans (C.recordRelabel_tp σ w)⟩

end CoherentCoordinates
/-- The discard constructed from the actual triple data recovers its supplied first-pair map. -/
theorem coherentCoordinatesOfTriple_marginal12 (hn : 0 < n)
    (hm : TensorNormalForm M U ε δ) (hl : TensorNormalForm L V α β)
    (hM : Spans M) (hL : Spans L)
    {r : H (n * n) →ₗ[ℝ] H n} {p12 p13 p23 : H (TripleSize n) →ₗ[ℝ] H (n * n)}
    (h : TripleMarginals M L r p12 p13 p23) :
    p12 = (coherentCoordinatesOfTriple hn hm hl hM hL h).marginal12 :=
  (coherentCoordinatesOfTriple hn hm hl hM hL h).marginal12_unique hL p12 h.read12

end PositiveMarginalMatrixComposition.TripleOrientation
