/- GID: D5/S3/Quantum/Fermionic/WeightedSlaterPairCut
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/WeightedSlaterPairCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact purity of an ordered Slater marginal from binary endpoint differences. -/

import D5.S3.Quantum.Fermionic.SlaterPairCutRank

/-! Endpoint differences determine the purity across the ordinary occupation cut. -/

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Fermionic.WeightedSlaterPairCut

open OrderedSlaterCut SlaterPairCutRank

variable {ι : Type*} [LinearOrder ι]

private theorem amplitude_on_selected_pairs {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hp : ∀ i, (p (i, false) : ι) < p (i, true))
    (hq : ∀ j, (q (j, false) : ι) < q (j, true))
    (weight : Fin (m + n) → Bool → ℂ) :
    let A := alternationMatrix (fun i e => (p (i, e) : ι)) (fun j e => (q (j, e) : ι))
    ∃ left : (Fin m → ZMod 2) → ZMod 2, ∃ right : (Fin n → ZMod 2) → ZMod 2,
      ∀ (x : Fin m → ZMod 2) (y : Fin n → ZMod 2),
        orderedCut I (cutPairOrbitals p q weight) (pairBitOccupation p x)
          (pairBitOccupation q y) =
          (binarySign (left x) * ∏ i, weight (Fin.castAdd n i) (pickEndpoint (x i))) *
            binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) *
            (binarySign (right y) * ∏ j, weight (Fin.natAdd m j) (pickEndpoint (y j))) := by
  intro A
  obtain ⟨left, right, hphase⟩ := orderedCut_pairs_character p q (1 : ℂ) hp hq
  refine ⟨left, right, fun x y => ?_⟩
  have hs := hphase x y
  rw [orderedCut_pairs_selected] at hs
  simp only [Finset.prod_const, one_pow, mul_one, one_mul] at hs
  have hw := orderedCut_pairs_selected p q weight
    (fun i => pickEndpoint (x i)) (fun j => pickEndpoint (y j))
  change orderedCut I (cutPairOrbitals p q weight) (pairBitOccupation p x)
    (pairBitOccupation q y) = _ at hw
  rw [hw, hs, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  dsimp [A]
  ring

omit [LinearOrder ι] in
private theorem weightedCharacter_purity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (a : (Fin m → ZMod 2) → ℂ) (b : (Fin n → ZMod 2) → ℂ) :
    let M : Matrix (Fin m → ZMod 2) (Fin n → ZMod 2) ℂ :=
      fun x y => a x * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) * b y
    ((M * Mᴴ) ^ 2).trace =
      ∑ x, ∑ x', (a x * star (a x)) * (a x' * star (a x')) *
        (∑ y, b y * star (b y) * binarySign ((Aᵀ *ᵥ (x + x')) ⬝ᵥ y)) ^ 2 := by
  intro M
  let N := M * Mᴴ
  let moment (z : Fin m → ZMod 2) : ℂ :=
    ∑ y, b y * star (b y) * binarySign ((Aᵀ *ᵥ z) ⬝ᵥ y)
  have hgram (x x' : Fin m → ZMod 2) :
      N x x' = a x * star (a x') * moment (x + x') := by
    dsimp only [N, moment]
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    change M x y * star (M x' y) = _
    simp only [M, star_mul', binarySign_star, Matrix.mulVec_add, add_dotProduct,
      AddChar.map_add_eq_mul]
    ac_rfl
  rw [pow_two]
  change (∑ x, ∑ x', N x x' * N x' x) = _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  change N x x' * N x' x =
    (a x * star (a x)) * (a x' * star (a x')) * moment (x + x') ^ 2
  rw [hgram x x', hgram x' x, add_comm x' x, pow_two]
  ac_rfl

omit [LinearOrder ι] in
private theorem weightedShift_purity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ZMod 2 → ℂ) (moment : (ι → ZMod 2) → ℂ) :
    (∑ x : ι → ZMod 2, ∑ x' : ι → ZMod 2,
      (∏ i, weight i (x i)) * (∏ i, weight i (x' i)) * moment (x + x') ^ 2) =
      ∑ z : ι → ZMod 2,
        (∏ i, ∑ v : ZMod 2, weight i v * weight i (v + z i)) * moment z ^ 2 := by
  classical
  have hshift (x : ι → ZMod 2) :
      (∑ x' : ι → ZMod 2,
        (∏ i, weight i (x i)) * (∏ i, weight i (x' i)) * moment (x + x') ^ 2) =
      ∑ z : ι → ZMod 2,
        (∏ i, weight i (x i)) * (∏ i, weight i (x i + z i)) * moment z ^ 2 := by
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ ?_
    intro x'
    have hx (i : ι) : x i + (x i + x' i) = x' i := by
      have hxx : x i + x i = 0 :=
        (congrArg (x i + ·) (ZMod.neg_eq_self_mod_two (x i))).symm.trans (add_neg_cancel _)
      rw [← add_assoc, hxx, zero_add]
    change _ = (∏ i, weight i (x i)) *
      (∏ i, weight i (x i + (x + x') i)) * moment (x + x') ^ 2
    simp only [Pi.add_apply, hx]
  simp_rw [hshift]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => weight i v * weight i (v + z i))).symm

omit [LinearOrder ι] in
private theorem weightedEndpoint_moment {n : ℕ} (d : Fin n → ZMod 2)
    (weight : Fin n → ZMod 2 → ℂ) :
    (∑ y : Fin n → ZMod 2, (∏ j, weight j (y j)) * binarySign (d ⬝ᵥ y)) =
      ∏ j, ∑ v : ZMod 2, weight j v * binarySign (d j * v) := by
  have hchar (y : Fin n → ZMod 2) :
      binarySign (d ⬝ᵥ y) = ∏ j, binarySign (d j * y j) := by
    change (binarySign.toAddMonoidHom (∑ j, d j * y j)).toMul =
      ∏ j, (binarySign.toAddMonoidHom (d j * y j)).toMul
    rw [map_sum, toMul_sum]
  simp_rw [hchar, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j v => weight j v * binarySign (d j * v))).symm

omit [LinearOrder ι] in
private theorem signedProduct_star {κ : Type*} [Fintype κ]
    (sign : ZMod 2) (weight : κ → ℂ) :
    (binarySign sign * ∏ i, weight i) * star (binarySign sign * ∏ i, weight i) =
      ∏ i, weight i * star (weight i) := by
  rw [star_mul', binarySign_star, star_prod]
  calc
    _ = (binarySign sign * binarySign sign) *
        ((∏ i, weight i) * ∏ i, star (weight i)) := by ac_rfl
    _ = _ := by rw [binarySign_sq, one_mul, ← Finset.prod_mul_distrib]

omit [LinearOrder ι] in
private theorem purity_isometric_padding {X Y U V : Type*}
    [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    [DecidableEq X] [DecidableEq U] [DecidableEq V]
    (E : Matrix X U ℂ) (F : Matrix Y V ℂ) (M : Matrix U V ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    let B := E * M * Fᴴ
    ((B * Bᴴ) ^ 2).trace = ((M * Mᴴ) ^ 2).trace := by
  intro B
  let G := M * Mᴴ
  have hGram : B * Bᴴ = E * G * Eᴴ := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = E * M * (Fᴴ * F) * Mᴴ * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hF, Matrix.mul_one, G, Matrix.mul_assoc]
  rw [hGram, pow_two, pow_two]
  calc
    _ = (E * G * (Eᴴ * E) * G * Eᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (G * G).trace := by
      rw [hE, Matrix.mul_one, Matrix.trace_mul_comm]
      simp only [← Matrix.mul_assoc, hE, Matrix.one_mul]

open Classical in
/-- The ordinary marginal purity of disjoint pairs is a product sum over binary
endpoint differences. Zero endpoint amplitudes are included. -/
theorem orderedMarginal_purity [Fintype ι] {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hp : ∀ i, (p (i, false) : ι) < p (i, true))
    (hq : ∀ j, (q (j, false) : ι) < q (j, true))
    (weight : Fin (m + n) → Bool → ℂ) :
    let A := alternationMatrix (fun i e => (p (i, e) : ι)) (fun j e => (q (j, e) : ι))
    let B := orderedCut I (cutPairOrbitals p q weight)
    let leftMass (i : Fin m) (v : ZMod 2) :=
      weight (Fin.castAdd n i) (pickEndpoint v) * star (weight (Fin.castAdd n i) (pickEndpoint v))
    let rightMass (j : Fin n) (v : ZMod 2) :=
      weight (Fin.natAdd m j) (pickEndpoint v) * star (weight (Fin.natAdd m j) (pickEndpoint v))
    ((B * Bᴴ) ^ 2).trace =
      ∑ z : Fin m → ZMod 2,
        (∏ i, ∑ v : ZMod 2, leftMass i v * leftMass i (v + z i)) *
          (∏ j, ∑ v : ZMod 2, rightMass j v * binarySign ((Aᵀ *ᵥ z) j * v)) ^ 2 := by
  intro A B leftMass rightMass
  obtain ⟨left, right, hphase⟩ := amplitude_on_selected_pairs p q hp hq weight
  let a (x : Fin m → ZMod 2) :=
    binarySign (left x) * ∏ i, weight (Fin.castAdd n i) (pickEndpoint (x i))
  let b (y : Fin n → ZMod 2) :=
    binarySign (right y) * ∏ j, weight (Fin.natAdd m j) (pickEndpoint (y j))
  let M : Matrix (Fin m → ZMod 2) (Fin n → ZMod 2) ℂ :=
    fun x y => a x * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) * b y
  have hpad := eq_padding (pairBitOccupation p) (pairBitOccupation q) B M
    (fun x y => hphase x y)
    (fun u v h => orderedCut_pairs_zero p q weight u v
      (Or.inl (not_pairOccupation_of_not_bit p h)))
    (fun u v h => orderedCut_pairs_zero p q weight u v
      (Or.inr (not_pairOccupation_of_not_bit q h)))
  rw [hpad, purity_isometric_padding _ _ _ (embed_adjoint_mul _) (embed_adjoint_mul _)]
  change ((M * Mᴴ) ^ 2).trace = _
  rw [weightedCharacter_purity A a b]
  have ha (x : Fin m → ZMod 2) : a x * star (a x) = ∏ i, leftMass i (x i) :=
    signedProduct_star (left x) (fun i => weight (Fin.castAdd n i) (pickEndpoint (x i)))
  have hb (y : Fin n → ZMod 2) : b y * star (b y) = ∏ j, rightMass j (y j) :=
    signedProduct_star (right y) (fun j => weight (Fin.natAdd m j) (pickEndpoint (y j)))
  simp_rw [ha, hb]
  refine (weightedShift_purity leftMass
    (fun z => ∑ y, (∏ j, rightMass j (y j)) * binarySign ((Aᵀ *ᵥ z) ⬝ᵥ y))).trans ?_
  simp_rw [weightedEndpoint_moment _ rightMass]

end D5.S3.Quantum.Fermionic.WeightedSlaterPairCut
