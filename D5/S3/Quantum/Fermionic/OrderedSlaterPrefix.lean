/- GID: D5/S3/Quantum/Fermionic/OrderedSlaterPrefix
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/OrderedSlaterPrefix
   mirror-E: none(waiver:finite-slater-marginal-spectrum)
   anchors: []
   utility: none
   digest: The full ordinary Slater marginal spectrum at an ordered cut -/

import D5.S3.Quantum.Fermionic.OrderedSlaterCut
import D5.S3.Quantum.Fermionic.SlaterPrefixContraction

/-! # The full ordinary Slater marginal spectrum at an ordered cut -/

namespace D5.S3.Quantum.Fermionic.OrderedSlaterPrefix
open scoped BigOperators
open Matrix Polynomial
open D5.S3.Quantum.Fermionic.OrderedSlaterCut D5.S3.Quantum.Fermionic.SlaterPrefixContraction

noncomputable local instance {ι : Type*} [Fintype ι] (I : Set ι) : Fintype (Occupation I) :=
  Fintype.ofFinite _

noncomputable local instance {ι : Type*} [Fintype ι] (I : Set ι) : Fintype I :=
  Fintype.ofFinite _

private def prefixSide (m n : ℕ) : Set (Fin (m + n)) := {i | i.val < m}

private def leftSiteEquiv (m n : ℕ) : Fin m ≃ prefixSide m n where
  toFun i := ⟨Fin.castAdd n i, i.isLt⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv i := by ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private def rightSiteEquiv (m n : ℕ) : Fin n ≃ ↑((prefixSide m n)ᶜ) where
  toFun i := ⟨Fin.natAdd m i, by change ¬ m + i.val < m; omega⟩
  invFun i := ⟨i.val.val - m, by
    have hi := i.val.isLt
    have hleft : ¬ i.val.val < m := i.property
    omega⟩
  left_inv i := by apply Fin.ext; change m + i.val - m = i.val; omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hi : ¬ i.val.val < m := i.property
    change m + (i.val.val - m) = i.val.val
    omega

private def prefixOccupationEquiv (m n : ℕ) : Finset (Fin m) ≃ Occupation (prefixSide m n) :=
  (leftSiteEquiv m n).finsetCongr.trans (Equiv.finsetSubtypeComm (· ∈ prefixSide m n))

private def tailOccupationEquiv (m n : ℕ) : Finset (Fin n) ≃ Occupation ((prefixSide m n)ᶜ) :=
  (rightSiteEquiv m n).finsetCongr.trans (Equiv.finsetSubtypeComm (· ∈ (prefixSide m n)ᶜ))

private theorem ordered_split_rows {m n : ℕ} (a : Finset (Fin m)) (b : Finset (Fin n))
    (h : Disjoint (a.map (Fin.castAddEmb n)) (b.map (Fin.natAddEmb m))) :
    let s := (a.map (Fin.castAddEmb n)).disjUnion (b.map (Fin.natAddEmb m)) h
    let hs : s.card = a.card + b.card := by
      simp only [s, Finset.card_disjUnion, Finset.card_map]
    (s.orderEmbOfFin hs : Fin (a.card + b.card) → Fin (m + n)) =
      Fin.addCases (fun i => Fin.castAdd n (a.orderEmbOfFin rfl i))
        (fun j => Fin.natAdd m (b.orderEmbOfFin rfl j)) := by
  intro s hs
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    induction x using Fin.addCases with
    | left i =>
      rw [Fin.addCases_left]
      exact Finset.mem_disjUnion.mpr (Or.inl
        (Finset.mem_map.mpr ⟨_, a.orderEmbOfFin_mem rfl i, rfl⟩))
    | right j =>
      rw [Fin.addCases_right]
      exact Finset.mem_disjUnion.mpr (Or.inr
        (Finset.mem_map.mpr ⟨_, b.orderEmbOfFin_mem rfl j, rfl⟩))
  · intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left]
        exact (a.orderEmbOfFin rfl).strictMono (show i < j from hij)
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right]
        have hi := (a.orderEmbOfFin rfl i).isLt
        change (a.orderEmbOfFin rfl i).val < m + (b.orderEmbOfFin rfl j).val
        omega
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        change a.card + i.val < j.val at hij
        omega
      | right j =>
        simp only [Fin.addCases_right]
        exact (Fin.natAdd_lt_natAdd_iff m).mpr
          ((b.orderEmbOfFin rfl).strictMono ((Fin.natAdd_lt_natAdd_iff _).mp hij))

private theorem prefixAmplitudes_orderedCut {m n k : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) :
    (orderedCut (prefixSide m n) (stackRows P Y)).submatrix
      (prefixOccupationEquiv m n) (tailOccupationEquiv m n) = prefixAmplitudes P Y := by
  classical
  ext a b : 1
  let a₀ := a.map (Fin.castAddEmb n)
  let b₀ := b.map (Fin.natAddEmb m)
  let u := prefixOccupationEquiv m n a
  let v := tailOccupationEquiv m n b
  have ha : u.val = a₀ := by
    change (a.map (leftSiteEquiv m n).toEmbedding).map
      ⟨Subtype.val, Subtype.val_injective⟩ = a₀
    rw [Finset.map_map]
    rfl
  have hb : v.val = b₀ := by
    change (b.map (rightSiteEquiv m n).toEmbedding).map
      ⟨Subtype.val, Subtype.val_injective⟩ = b₀
    rw [Finset.map_map]
    rfl
  have hd₀ : Disjoint u.val v.val := Finset.disjoint_left.mpr
    (fun _ hx hy => v.property hy (u.property hx))
  have hcard : a₀.card + b₀.card = a.card + b.card := by simp [a₀, b₀]
  suffices htransport : ∀ (A B : Finset (Fin (m + n))), A = a₀ → B = b₀ →
      ∀ hd : Disjoint A B,
        (if h : A.card + B.card = k then
          ((stackRows P Y).submatrix
            ((A.disjUnion B hd).orderEmbOfFin ((Finset.card_disjUnion _ _ hd).trans h)) id).det
          else 0) = prefixAmplitudes P Y a b from
    htransport u.val v.val ha hb hd₀
  intro A B hA hB hd
  subst A
  subst B
  by_cases hk : a.card + b.card = k
  · rw [dite_eq_left (hcard.trans hk)]
    unfold prefixAmplitudes
    rw [dite_eq_left hk]
    congr 1
    ext i j : 1
    have hrow := ordered_split_rows a b hd
    have hpos := congrFun hrow (Fin.cast hk.symm i)
    change (a₀.disjUnion b₀ hd).orderEmbOfFin ((Finset.card_disjUnion _ _ hd).trans
      (hcard.trans hk)) i = _ at hpos
    change stackRows P Y ((a₀.disjUnion b₀ hd).orderEmbOfFin _ i) j =
      stackRows (P.submatrix (a.orderEmbOfFin rfl) id)
        (Y.submatrix (b.orderEmbOfFin rfl) id) (Fin.cast hk.symm i) j
    rw [hpos]
    generalize Fin.cast hk.symm i = r
    induction r using Fin.addCases with
    | left r => simp [stackMinor, stackRows]
    | right r => simp [stackMinor, stackRows]
  · simp [prefixAmplitudes, hcard, hk]


private def occupationSectorEquiv (m : ℕ) :
    (Σ r : Fin (m + 1), {a : Finset (Fin m) // a.card = r.val}) ≃ Finset (Fin m) where
  toFun a := a.2.val
  invFun a := ⟨⟨a.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ a)⟩, ⟨a, rfl⟩⟩
  left_inv a := by
    obtain ⟨⟨r, hr⟩, ⟨a, ha⟩⟩ := a
    change a.card = r at ha
    subst r
    rfl
  right_inv _ := rfl

private noncomputable def orderedCompound {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (r : ℕ) :
    Matrix {a : Finset (Fin m) // a.card = r} {a : Finset (Fin m) // a.card = r} ℂ :=
  fun a b => (U.submatrix (a.val.orderEmbOfFin a.property) (b.val.orderEmbOfFin b.property)).det

private theorem orderedCompound_mul {m : ℕ} (U V : Matrix (Fin m) (Fin m) ℂ) (r : ℕ) :
    orderedCompound (U * V) r = orderedCompound U r * orderedCompound V r := by
  classical
  ext1 a b
  rw [Matrix.mul_apply]
  simp only [orderedCompound]
  rw [Matrix.submatrix_mul U V _ id _ Function.bijective_id]
  exact cauchyBinet _ _

private theorem orderedCompound_conjTranspose {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (r : ℕ) :
    orderedCompound U.conjTranspose r = (orderedCompound U r).conjTranspose := by
  ext1 a b
  simp only [orderedCompound, Matrix.conjTranspose_apply, ← Matrix.det_conjTranspose,
    Matrix.conjTranspose_submatrix]

private theorem orderedCompound_one (m r : ℕ) :
    orderedCompound (1 : Matrix (Fin m) (Fin m) ℂ) r = 1 := by
  classical
  ext1 a b
  by_cases h : a = b
  · subst b
    rw [Matrix.one_apply_eq]
    unfold orderedCompound
    have he :
        (1 : Matrix (Fin m) (Fin m) ℂ).submatrix (a.val.orderEmbOfFin a.property)
          (a.val.orderEmbOfFin a.property) = 1 := by
      ext i j
      simp [Matrix.one_apply, (a.val.orderEmbOfFin a.property).injective.eq_iff]
    simp [he]
  · rw [Matrix.one_apply_ne h]
    unfold orderedCompound
    have hn : ¬ a.val ⊆ b.val := fun hsub =>
      h (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [a.property, b.property])))
    obtain ⟨x, hx, hnot⟩ := Finset.not_subset.mp hn
    let i := (a.val.orderIsoOfFin a.property).symm ⟨x, hx⟩
    have hi : a.val.orderEmbOfFin a.property i = x :=
      congrArg Subtype.val ((a.val.orderIsoOfFin a.property).apply_symm_apply ⟨x, hx⟩)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    have hne : x ≠ b.val.orderEmbOfFin b.property j := fun he =>
      hnot (he ▸ b.val.orderEmbOfFin_mem b.property j)
    simp [Matrix.submatrix_apply, Matrix.one_apply, hi, hne]

private noncomputable def occupationUnitaryLift {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Finset (Fin m)) (Finset (Fin m)) ℂ := by
  classical
  exact Matrix.reindex (occupationSectorEquiv m) (occupationSectorEquiv m)
    (Matrix.blockDiagonal' (fun r : Fin (m + 1) => orderedCompound U r.val))

private theorem occupationUnitaryLift_isometry {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.conjTranspose * U = 1) :
    (occupationUnitaryLift U).conjTranspose * occupationUnitaryLift U = 1 := by
  classical
  have hsector (r : Fin (m + 1)) :
      (orderedCompound U r.val).conjTranspose * orderedCompound U r.val = 1 := by
    rw [← orderedCompound_conjTranspose, ← orderedCompound_mul, hU, orderedCompound_one]
  simp only [occupationUnitaryLift, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp only [hsector]
  change (Matrix.blockDiagonal' (1 : ∀ r : Fin (m + 1),
    Matrix {a : Finset (Fin m) // a.card = r.val} {a : Finset (Fin m) // a.card = r.val} ℂ)).submatrix
      (occupationSectorEquiv m).symm (occupationSectorEquiv m).symm = 1
  rw [Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]


private def retainedBasisBlock {r m : ℕ} (t : ℕ) (A : Matrix (Fin r) (Fin m) ℂ) :
    Matrix (Fin (r + t)) (Fin (m + t)) ℂ :=
  fun i => Fin.addCases
    (fun j => Fin.addCases (A j) (fun _ => 0))
    (fun j => Fin.addCases (fun _ => 0) (fun q => if j = q then 1 else 0)) i

private theorem stackRows_basisBlock_mul {r m t k : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ) (P : Matrix (Fin m) (Fin k) ℂ)
    (Z : Matrix (Fin t) (Fin k) ℂ) :
    retainedBasisBlock t A * stackRows P Z = stackRows (A * P) Z := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  induction i using Fin.addCases with
  | left i => simp [retainedBasisBlock, stackRows, Matrix.mul_apply]
  | right i => simp [retainedBasisBlock, stackRows]

private theorem det_basisBlock_minor_of_missing_tail {r m t : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ) (S : Finset (Fin (m + t))) (hS : S.card = r + t)
    (j : Fin t) (hj : Fin.natAdd m j ∉ S) :
    ((retainedBasisBlock t A).submatrix id (S.orderEmbOfFin hS)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (Fin.natAdd r j)
  intro i
  change retainedBasisBlock t A (Fin.natAdd r j) (S.orderEmbOfFin hS i) = 0
  have hi := S.orderEmbOfFin_mem hS i
  generalize (S.orderEmbOfFin hS) i = q at hi ⊢
  induction q using Fin.addCases with
  | left q => simp [retainedBasisBlock, Matrix.submatrix_apply]
  | right q =>
    have hne : j ≠ q := fun h => hj (h ▸ hi)
    simp [retainedBasisBlock, Matrix.submatrix_apply, hne]


private def fullTail (m t : ℕ) : Finset (Fin (m + t)) :=
  Finset.univ.map (Fin.natAddEmb m)

private noncomputable def frontSites {m t : ℕ} (S : Finset (Fin (m + t))) : Finset (Fin m) :=
  S.preimage (Fin.castAddEmb t) (Fin.castAddEmb t).injective.injOn

private theorem front_fullTail_disjoint {m t : ℕ} (a : Finset (Fin m)) :
    Disjoint (a.map (Fin.castAddEmb t)) (fullTail m t) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
  have h := congrArg Fin.val (hi.trans hj.symm)
  change i.val = m + j.val at h
  omega

private theorem front_fullTail_recover {m t : ℕ} (S : Finset (Fin (m + t)))
    (hS : fullTail m t ⊆ S) :
    ((frontSites S).map (Fin.castAddEmb t)).disjUnion (fullTail m t)
      (front_fullTail_disjoint _) = S := by
  ext x
  induction x using Fin.addCases with
  | left i =>
    have h : Fin.castAddEmb t i ∉ fullTail m t := fun hi =>
      Finset.disjoint_left.mp (front_fullTail_disjoint ({i} : Finset (Fin m)))
        (Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩) hi
    change Fin.castAddEmb t i ∈ _ ↔ Fin.castAddEmb t i ∈ S
    simp only [Finset.mem_disjUnion, h, or_false, Finset.mem_map', frontSites, Finset.mem_preimage]
  | right j =>
    have h : Fin.natAdd m j ∈ fullTail m t :=
      Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
    simp [h, hS h]

private noncomputable def tailContainingSubsets (r m t : ℕ) :
    {S : {S : Finset (Fin (m + t)) // S.card = r + t} // fullTail m t ⊆ S.val} ≃
      {a : Finset (Fin m) // a.card = r} where
  toFun S := ⟨frontSites S.val.val, by
    have h := congrArg Finset.card (front_fullTail_recover S.val.val S.property)
    apply Nat.add_right_cancel (m := t)
    simpa only [Finset.card_disjUnion, Finset.card_map, fullTail, Finset.card_univ,
      Fintype.card_fin, S.val.property] using h⟩
  invFun a := ⟨⟨(a.val.map (Fin.castAddEmb t)).disjUnion (fullTail m t)
      (front_fullTail_disjoint a.val), by
    simp only [Finset.card_disjUnion, Finset.card_map, fullTail, Finset.card_univ,
      Fintype.card_fin, a.property]⟩, by
    intro x hx
    change x ∈ (a.val.map (Fin.castAddEmb t)).disjUnion (fullTail m t)
      (front_fullTail_disjoint a.val)
    exact Finset.mem_disjUnion.mpr (Or.inr hx)⟩
  left_inv S := Subtype.ext (Subtype.ext (front_fullTail_recover S.val.val S.property))
  right_inv a := by
    apply Subtype.ext
    ext i
    have h : Fin.castAddEmb t i ∉ fullTail m t := fun hi =>
      Finset.disjoint_left.mp (front_fullTail_disjoint ({i} : Finset (Fin m)))
        (Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩) hi
    change i ∈ frontSites ((a.val.map (Fin.castAddEmb t)).disjUnion (fullTail m t)
      (front_fullTail_disjoint a.val)) ↔ i ∈ a.val
    simp only [frontSites, Finset.mem_preimage, Finset.mem_disjUnion, h, or_false, Finset.mem_map']


private theorem ordered_basis_columns {r m t : ℕ} (a : {a : Finset (Fin m) // a.card = r}) :
    let S := (tailContainingSubsets r m t).symm a
    (S.val.val.orderEmbOfFin S.val.property : Fin (r + t) → Fin (m + t)) =
      Fin.addCases (fun i => Fin.castAdd t (a.val.orderEmbOfFin a.property i)) (Fin.natAdd m) := by
  intro S
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    change _ ∈ (a.val.map (Fin.castAddEmb t)).disjUnion (fullTail m t)
      (front_fullTail_disjoint a.val)
    induction x using Fin.addCases with
    | left i =>
      rw [Fin.addCases_left]
      exact Finset.mem_disjUnion.mpr (Or.inl
        (Finset.mem_map.mpr ⟨_, a.val.orderEmbOfFin_mem a.property i, rfl⟩))
    | right j =>
      rw [Fin.addCases_right]
      exact Finset.mem_disjUnion.mpr (Or.inr (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  · intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left]
        exact (a.val.orderEmbOfFin a.property).strictMono (show i < j from hij)
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right]
        have hi := (a.val.orderEmbOfFin a.property i).isLt
        change (a.val.orderEmbOfFin a.property i).val < m + j.val
        omega
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        change r + i.val < j.val at hij
        omega
      | right j =>
        simp only [Fin.addCases_right]
        exact (Fin.natAdd_lt_natAdd_iff m).mpr ((Fin.natAdd_lt_natAdd_iff r).mp hij)

private theorem det_basisBlock_minor {r m t : ℕ} (A : Matrix (Fin r) (Fin m) ℂ)
    (a : {a : Finset (Fin m) // a.card = r}) :
    let S := (tailContainingSubsets r m t).symm a
    ((retainedBasisBlock t A).submatrix id (S.val.val.orderEmbOfFin S.val.property)).det =
      (A.submatrix id (a.val.orderEmbOfFin a.property)).det := by
  classical
  intro S
  let f := S.val.val.orderEmbOfFin S.val.property
  let e : Fin r ⊕ Fin t ≃ Fin (r + t) := finSumFinEquiv
  let B := Matrix.fromBlocks (A.submatrix id (a.val.orderEmbOfFin a.property))
    (0 : Matrix (Fin r) (Fin t) ℂ) (0 : Matrix (Fin t) (Fin r) ℂ)
    (1 : Matrix (Fin t) (Fin t) ℂ)
  have hB : ((retainedBasisBlock t A).submatrix id f).submatrix e e = B := by
    ext i j : 1
    have hf := ordered_basis_columns (t := t) a
    change (f : Fin (r + t) → Fin (m + t)) = _ at hf
    change retainedBasisBlock t A (e i) (f (e j)) = B i j
    rw [congrFun hf (e j)]
    cases i <;> cases j <;>
      simp [B, e, retainedBasisBlock, Matrix.submatrix_apply, Matrix.one_apply]
  calc
    _ = (((retainedBasisBlock t A).submatrix id f).submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self _ _).symm
    _ = B.det := congrArg Matrix.det hB
    _ = _ := by simp [B]


private theorem stackedMinor_left_basis_expansion {r m t : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ) (P : Matrix (Fin m) (Fin (r + t)) ℂ)
    (Z : Matrix (Fin t) (Fin (r + t)) ℂ) :
    (stackRows (A * P) Z).det =
      ∑ a : {a : Finset (Fin m) // a.card = r},
        (A.submatrix id (a.val.orderEmbOfFin a.property)).det *
          (stackRows (P.submatrix (a.val.orderEmbOfFin a.property) id) Z).det := by
  classical
  rw [← stackRows_basisBlock_mul, cauchyBinet]
  let f (S : {S : Finset (Fin (m + t)) // S.card = r + t}) :=
    ((retainedBasisBlock t A).submatrix id (S.val.orderEmbOfFin S.property)).det *
      ((stackRows P Z).submatrix (S.val.orderEmbOfFin S.property) id).det
  have hfilter : ∑ S, f S =
      ∑ S ∈ Finset.univ.filter (fun S => fullTail m t ⊆ S.val), f S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hmissing : ¬ fullTail m t ⊆ S.val := fun h => hS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨i, hi, hnot⟩ := Finset.not_subset.mp hmissing
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact mul_eq_zero_of_left
      (det_basisBlock_minor_of_missing_tail A S.val S.property j hnot) _
  change (∑ S, f S) = _
  rw [hfilter, ← Finset.sum_subtype_eq_sum_filter]
  have hu : (Finset.univ : Finset {S : {S : Finset (Fin (m + t)) // S.card = r + t} //
      fullTail m t ⊆ S.val}) =
      Finset.univ.subtype (fun S : {S : Finset (Fin (m + t)) // S.card = r + t} =>
        fullTail m t ⊆ S.val) := by
    ext S
    simp
  rw [← hu]
  apply Fintype.sum_equiv (tailContainingSubsets r m t)
  intro S
  let a := tailContainingSubsets r m t S
  change f S = _
  have he : (tailContainingSubsets r m t).symm a = S := by simp [a]
  have hleft := det_basisBlock_minor (t := t) A a
  change ((retainedBasisBlock t A).submatrix id
    (((tailContainingSubsets r m t).symm a).val.val.orderEmbOfFin
      ((tailContainingSubsets r m t).symm a).val.property)).det = _ at hleft
  rw [he] at hleft
  have hright : (stackRows P Z).submatrix (S.val.val.orderEmbOfFin S.val.property) id =
      stackRows (P.submatrix (a.val.orderEmbOfFin a.property) id) Z := by
    have horder := ordered_basis_columns (t := t) a
    change (((tailContainingSubsets r m t).symm a).val.val.orderEmbOfFin
      ((tailContainingSubsets r m t).symm a).val.property : Fin (r + t) → _) = _ at horder
    rw [he] at horder
    ext i j : 1
    change stackRows P Z (S.val.val.orderEmbOfFin S.val.property i) j = _
    rw [congrFun horder i]
    induction i using Fin.addCases with
    | left i => simp [stackRows, Matrix.submatrix_apply]
    | right i => simp [stackRows]
  simp only [f, hleft, hright, a]


private theorem stackMinor_left_basis_expansion {r m n k : ℕ}
    (A : Matrix (Fin r) (Fin m) ℂ) (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (b : Finset (Fin n)) (hb : r + b.card = k) :
    (stackMinor (A * P) Y b hb).det =
      ∑ a : {a : Finset (Fin m) // a.card = r},
        (A.submatrix id (a.val.orderEmbOfFin a.property)).det *
          (stackMinor (P.submatrix (a.val.orderEmbOfFin a.property) id) Y b hb).det := by
  subst k
  simpa [stackMinor] using
    stackedMinor_left_basis_expansion A P (Y.submatrix (b.orderEmbOfFin rfl) id)

private theorem occupationUnitaryLift_apply {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (a b : Finset (Fin m)) :
    occupationUnitaryLift U a b = if h : b.card = a.card then
      (U.submatrix (a.orderEmbOfFin rfl) (b.orderEmbOfFin h)).det else 0 := by
  classical
  let rank (a : Finset (Fin m)) : Fin (m + 1) :=
    ⟨a.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ a)⟩
  let family (r : Fin (m + 1)) := {a : Finset (Fin m) // a.card = r.val}
  change (Matrix.blockDiagonal' (fun r : Fin (m + 1) => orderedCompound U r.val))
      ⟨rank a, ⟨a, rfl⟩⟩ ⟨rank b, ⟨b, rfl⟩⟩ = _
  rw [Matrix.blockDiagonal'_apply']
  by_cases he : b.card = a.card
  · have he' : rank a = rank b := Fin.ext he.symm
    rw [dite_eq_left he, dite_eq_left he']
    have hcast (i j : Fin (m + 1)) (h : i = j) (x : family i) :
        cast (congrArg family h) x = ⟨x.val, x.property.trans (congrArg Fin.val h)⟩ := by
      subst j
      rfl
    rw [hcast (rank b) (rank a) he'.symm] <;> rfl
  · rw [dite_eq_right he, dite_eq_right (fun h => he (congrArg Fin.val h).symm)]



private theorem prefixAmplitudes_basisAction {m n k : ℕ}
    (U : Matrix (Fin m) (Fin m) ℂ) (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) :
    prefixAmplitudes (U * P) Y = occupationUnitaryLift U * prefixAmplitudes P Y := by
  classical
  ext a b : 1
  rw [Matrix.mul_apply]
  let g (c : Finset (Fin m)) := occupationUnitaryLift U a c * prefixAmplitudes P Y c b
  change _ = ∑ c, g c
  by_cases hab : a.card + b.card = k
  · let A := U.submatrix (a.orderEmbOfFin rfl) id
    have hA : (U * P).submatrix (a.orderEmbOfFin rfl) id = A * P := by
      rw [Matrix.submatrix_mul U P _ id _ Function.bijective_id]
      rfl
    conv_lhs => unfold prefixAmplitudes; rw [dite_eq_left hab, hA]
    rw [stackMinor_left_basis_expansion]
    have hu : (Finset.univ : Finset {c : Finset (Fin m) // c.card = a.card}) =
        (Finset.univ : Finset (Finset (Fin m))).subtype (fun c => c.card = a.card) := by
      ext c
      simp
    have hfilter : ∑ c, g c = ∑ c : {c : Finset (Fin m) // c.card = a.card}, g c.val := by
      rw [hu, Finset.sum_subtype_eq_sum_filter]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro c _ hc
      have hn : c.card ≠ a.card := fun h => hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [g, occupationUnitaryLift_apply, hn]
    rw [hfilter]
    apply Finset.sum_congr rfl
    intro c _
    have hb : c.val.card + b.card = k := by simpa only [c.property] using hab
    simp only [g, occupationUnitaryLift_apply, c.property, dite_eq_left, prefixAmplitudes, hab]
    have hs := stackMinor_cast_selected P Y c.val c.property b hab hb
    change (A.submatrix id (c.val.orderEmbOfFin c.property)).det *
        (stackMinor (P.submatrix (c.val.orderEmbOfFin c.property) id) Y b hab).det =
      (A.submatrix id (c.val.orderEmbOfFin c.property)).det *
        (stackMinor (P.submatrix (c.val.orderEmbOfFin rfl) id) Y b hb).det
    exact congrArg (fun M : Matrix (Fin k) (Fin k) ℂ =>
      (A.submatrix id (c.val.orderEmbOfFin c.property)).det * M.det) hs.symm
  · simp only [prefixAmplitudes, dite_eq_right hab]
    symm
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c.card = a.card
    · have hb : c.card + b.card ≠ k := by simpa only [hc] using hab
      simp [g, prefixAmplitudes, hb]
    · simp [g, occupationUnitaryLift_apply, hc]


private theorem prefixMarginal_basisAction_charpoly {m n k : ℕ}
    (U : Matrix (Fin m) (Fin m) ℂ) (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (hU : U.conjTranspose * U = 1) :
    ((prefixAmplitudes (U * P) Y) * (prefixAmplitudes (U * P) Y).conjTranspose).charpoly =
      ((prefixAmplitudes P Y) * (prefixAmplitudes P Y).conjTranspose).charpoly := by
  let L := occupationUnitaryLift U
  let M := prefixAmplitudes P Y
  have hL : L.conjTranspose * L = 1 := occupationUnitaryLift_isometry U hU
  rw [prefixAmplitudes_basisAction, Matrix.conjTranspose_mul]
  change ((L * M) * (M.conjTranspose * L.conjTranspose)).charpoly =
    (M * M.conjTranspose).charpoly
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc M M.conjTranspose,
    Matrix.charpoly_mul_comm L, Matrix.mul_assoc, hL, Matrix.mul_one]


private theorem stackRows_gram {m n k : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) :
    (stackRows P Y).conjTranspose * stackRows P Y =
      P.conjTranspose * P + Y.conjTranspose * Y := by
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply, Fin.sum_univ_add]
  simp [stackRows]

private theorem prefixMarginal_eigenvalue_product {m n k : ℕ}
    (P : Matrix (Fin m) (Fin k) ℂ) (Y : Matrix (Fin n) (Fin k) ℂ)
    (hV : P.conjTranspose * P + Y.conjTranspose * Y = 1) :
    let hP : (P * P.conjTranspose).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self P
    let ν : Fin m → ℂ := fun i => (hP.eigenvalues i : ℂ)
    (prefixAmplitudes P Y * (prefixAmplitudes P Y).conjTranspose).charpoly =
      ∏ a : Finset (Fin m), (X - C (∏ i : Fin m, if i ∈ a then ν i else 1 - ν i)) := by
  classical
  intro hP ν
  let E := hP.eigenvectorUnitary
  let U : Matrix (Fin m) (Fin m) ℂ := (E : Matrix (Fin m) (Fin m) ℂ).conjTranspose
  have hUE : U.conjTranspose = (E : Matrix (Fin m) (Fin m) ℂ) :=
    Matrix.conjTranspose_conjTranspose _
  have hU : U.conjTranspose * U = 1 := by
    rw [hUE]
    exact Unitary.coe_mul_star_self E
  have hdiag : (U * P) * (U * P).conjTranspose = Matrix.diagonal ν := by
    have hs := hP.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at hs
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, hUE]
    exact hs
  have hNew : (U * P).conjTranspose * (U * P) + Y.conjTranspose * Y = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc P.conjTranspose,
      ← Matrix.mul_assoc U.conjTranspose, hU, Matrix.one_mul, hV]
  rw [← prefixMarginal_basisAction_charpoly U P Y hU, diagonal_prefixMarginal _ _ _ hNew hdiag,
    Matrix.charpoly_diagonal]


private theorem factorLabels_perm {m : ℕ} (ν μ : Fin m → ℂ)
    (h : ∏ i, (X - C (ν i)) = ∏ i, (X - C (μ i))) :
    ∃ e : Equiv.Perm (Fin m), ∀ i, ν i = μ (e i) := by
  classical
  have roots_eq (f : Fin m → ℂ) :
      (∏ i, (X - C (f i))).roots = (Finset.univ : Finset (Fin m)).val.map f := by
    rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
      (fun i _ => Polynomial.X_sub_C_ne_zero (f i)))]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have hr := congrArg Polynomial.roots h
  rw [roots_eq ν, roots_eq μ] at hr
  let fib (z : ℂ) : {i : Fin m // ν i = z} ≃ {i : Fin m // μ i = z} :=
    Fintype.equivOfCardEq (by
      have hc := congrArg (Multiset.count z) hr
      rw [Multiset.count_map, Multiset.count_map] at hc
      rw [Fintype.card_subtype, Fintype.card_subtype]
      simpa only [Finset.filter_val, Finset.card, eq_comm] using hc)
  let e := (Equiv.sigmaFiberEquiv ν).symm.trans
    ((Equiv.sigmaCongrRight fib).trans (Equiv.sigmaFiberEquiv μ))
  exact ⟨e, fun i => ((fib (ν i)) ⟨i, rfl⟩).property.symm⟩

private theorem productSpectrum_relabel_modes {m : ℕ} (ν μ : Fin m → ℂ)
    (h : ∏ i, (X - C (ν i)) = ∏ i, (X - C (μ i))) :
    (∏ a : Finset (Fin m), (X - C (∏ i : Fin m, if i ∈ a then ν i else 1 - ν i))) =
      ∏ a : Finset (Fin m), (X - C (∏ i : Fin m, if i ∈ a then μ i else 1 - μ i)) := by
  classical
  obtain ⟨e, he⟩ := factorLabels_perm ν μ h
  apply Fintype.prod_equiv e.finsetCongr
  intro a
  congr 2
  apply Fintype.prod_equiv e
  intro i
  simp [Equiv.finsetCongr_apply, Finset.mem_map_equiv, he i]


theorem prefix_product_spectrum (m n k : ℕ) (W : Matrix (Fin (m + n)) (Fin k) ℂ)
    (hW : W.conjTranspose * W = 1) : HasProductSpectrum (prefixSide m n) W := by
  classical
  let I := prefixSide m n
  let P := W.submatrix (Fin.castAdd n) id
  let Y := W.submatrix (Fin.natAdd m) id
  have hstack : stackRows P Y = W := by
    ext i j : 1
    induction i using Fin.addCases with
    | left i => simp [stackRows, P, Matrix.submatrix_apply]
    | right i => simp [stackRows, Y, Matrix.submatrix_apply]
  have hV : P.conjTranspose * P + Y.conjTranspose * Y = 1 := by
    rw [← stackRows_gram, hstack, hW]
  intro ν hν
  let l := leftSiteEquiv m n
  let e := prefixOccupationEquiv m n
  let f := tailOccupationEquiv m n
  let M := orderedCut I W
  let Q := retainedRows I W
  have hM : M.submatrix e f = prefixAmplitudes P Y := by
    simpa only [hstack] using prefixAmplitudes_orderedCut P Y
  have hc : Q.submatrix l id = P := by rfl
  have hroots : (P * P.conjTranspose).charpoly = ∏ i : Fin m, (X - C (ν (l i))) := by
    rw [← hc, Matrix.conjTranspose_submatrix]
    change ((Q.submatrix l (Equiv.refl _)) *
      (Q.conjTranspose.submatrix (Equiv.refl _) l)).charpoly = _
    rw [Matrix.submatrix_mul_equiv]
    change (Matrix.reindex l.symm l.symm (Q * Q.conjTranspose)).charpoly = _
    rw [Matrix.charpoly_reindex, hν]
    exact (Fintype.prod_equiv l _ _ (fun _ => rfl)).symm
  let hP : (P * P.conjTranspose).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self P
  let μ : Fin m → ℂ := fun i => (hP.eigenvalues i : ℂ)
  have hcanonical : ∏ i : Fin m, (X - C (μ i)) = ∏ i : Fin m, (X - C (ν (l i))) := by
    exact hP.charpoly_eq.symm.trans hroots
  have htrace : (M * M.conjTranspose).charpoly =
      (prefixAmplitudes P Y * (prefixAmplitudes P Y).conjTranspose).charpoly := by
    rw [← hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    change _ = (Matrix.reindex e.symm e.symm (M * M.conjTranspose)).charpoly
    exact (Matrix.charpoly_reindex _ _).symm
  change (M * M.conjTranspose).charpoly = _
  rw [htrace, prefixMarginal_eigenvalue_product P Y hV]
  refine (productSpectrum_relabel_modes μ (ν ∘ l) hcanonical).trans ?_
  apply Fintype.prod_equiv e
  intro a
  congr 2
  unfold bernoulliWeight
  apply Fintype.prod_equiv l
  intro i
  have ha : (e a).val = a.map (Fin.castAddEmb n) := by
    change (a.map (leftSiteEquiv m n).toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩ = _
    rw [Finset.map_map]
    rfl
  rw [ha]
  simp [l, leftSiteEquiv, Finset.mem_map']

/-- The full ordinary tensor marginal has the occupation product spectrum for
every column-orthonormal Slater input exactly when the cut has no alternating
four-site subsequence. -/
theorem universal_cut_product_iff {ι : Type*} [LinearOrder ι] [Fintype ι] (I : Set ι) :
    ¬ D5.S3.Quantum.Fermionic.SlaterCutPhase.Alternates I ↔
      ∀ (k : ℕ) (V : Matrix ι (Fin k) ℂ), V.conjTranspose * V = 1 → HasProductSpectrum I V :=
  universal_cut_product_iff_of_prefix prefix_product_spectrum I

end D5.S3.Quantum.Fermionic.OrderedSlaterPrefix
