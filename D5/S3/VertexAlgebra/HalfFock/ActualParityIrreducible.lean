/- GID: D5/S3/VertexAlgebra/HalfFock/ActualParityIrreducible
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualParityIrreducible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-source physical modes act irreducibly on each entire actual parity sector. -/

/- proof_shape: fixedParitySlice_irreducible: content
admission_basis: escape-witness
escape_witness: A finite triangular Borcherds induction puts every ordered product
in the span of its original source iterates. Applied to even/odd source pairs,
it makes the sector submodule plus its odd images stable under every full-field
coefficient, while opposite target parity recovers the original intersection.
Classical order-two twisted lattice module irreducibility; no novelty claim. -/
import D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure

/-! Finite original-source Borcherds elimination and entire actual parity-sector closure. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockGroundRightCurrentTransport
open LatticeHalfFockGroundRightCurrentTransport.Calculus
open LatticeInvolution LatticeHalfFockParityT LatticeHalfFockParityField

open private upper high from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

/-- Finite triangular elimination uses the actual truncations at the same vector.
The second family vanishes and the non-leading first terms have smaller distance
from B's cutoff. All signed modes and the original finite supports are retained. -/
private theorem product_mem_of_iterates {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M) (gamma : ℤ)
    (law : fullLaw A B U gamma) (W : Submodule ℂ M) (w : M)
    (iterates : ∀ r k : ℤ, ((U r)[[k]]) w ∈ W) (m n : ℤ) :
    (A[[m]]) ((B[[n]]) w) ∈ W := by
  classical
  let K := upper B w
  have inductionStep : ∀ d : ℕ, ∀ n : ℤ, ((K : ℤ)-n).toNat = d →
      ∀ m : ℤ, (A[[m]]) ((B[[n]]) w) ∈ W := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro n distance m
      by_cases outside : (K : ℤ) ≤ n
      · rw [high B w n outside, map_zero]
        exact W.zero_mem
      let l : ℤ := upper A w
      let r := m-l
      obtain ⟨leftFinite, firstFinite, secondFinite, identity⟩ := law l n r w
      have secondZero (j : ℕ) : secondTerm A B l n r w j = 0 := by
        simp only [secondTerm, high A w (l+j) (by dsimp [l]; omega),
          map_zero, smul_zero]
      have secondSum : (∑ᶠ j : ℕ, secondTerm A B l n r w j) = 0 :=
        finsum_eq_zero_of_forall_eq_zero secondZero
      have leftMem : (∑ᶠ j : ℕ, leftTerm U gamma l n r w j) ∈ W := by
        rw [finsum_eq_sum_of_support_subset _ leftFinite.coe_toFinset.ge]
        apply W.sum_mem
        intro j hj
        exact W.smul_mem _ (iterates _ _)
      rw [secondSum, sub_zero] at identity
      rw [identity] at leftMem
      let F := insert 0 firstFinite.toFinset
      have firstSum : (∑ᶠ j : ℕ, firstTerm A B l n r w j) =
          ∑ j ∈ F, firstTerm A B l n r w j := by
        apply finsum_eq_sum_of_support_subset
        exact firstFinite.coe_toFinset.ge.trans (by intro j hj; exact Finset.mem_insert_of_mem hj)
      rw [firstSum] at leftMem
      have tailMem : (∑ j ∈ F.erase 0, firstTerm A B l n r w j) ∈ W := by
        apply W.sum_mem
        intro j hj
        have nonzero : j ≠ 0 := (Finset.mem_erase.mp hj).1
        have smaller : ((K : ℤ)-(n+j)).toNat < d := by omega
        have term := ih _ smaller (n+j) rfl (m-j)
        have indices : l+r-j = m-j := by dsimp [r]; omega
        simpa only [firstTerm, indices] using W.smul_mem (residueWeight r j) term
      have leading := W.sub_mem leftMem tailMem
      rw [← Finset.sum_erase_add F _ (Finset.mem_insert_self 0 firstFinite.toFinset)] at leading
      have headIndex : l+r = m := by dsimp [r]; omega
      simpa [firstTerm, residueWeight, headIndex] using leading
  exact inductionStep _ n rfl m


private abbrev slice (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (g : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  physicalSlice D hu (correctedField D hu a) g

private def lifted (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (S : Submodule ℂ (paritySpace D hu s)) : Submodule ℂ (ActualTensor D hu) :=
  S.map (paritySpace D hu s).subtype

private def oddImages (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (S : Submodule ℂ (paritySpace D hu s)) : Set (ActualTensor D hu) :=
  {y | ∃ a : Carrier D, theta D a = -a ∧ ∃ (n : ℤ) (x : ActualTensor D hu),
    x ∈ lifted D hu s S ∧ (slice D hu a 1)[[n]] x = y}

private def oddSpan (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (S : Submodule ℂ (paritySpace D hu s)) : Submodule ℂ (ActualTensor D hu) :=
  Submodule.span ℂ (oddImages D hu s S)

private theorem mem_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (x : ActualTensor D hu) :
    x ∈ paritySpace D hu s ↔ actualParity D hu x = s • x := by
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private theorem lifted_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (S : Submodule ℂ (paritySpace D hu s))
    (x : ActualTensor D hu) (hx : x ∈ lifted D hu s S) :
    actualParity D hu x = s • x := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact (mem_parity D hu s v).mp v.property

private theorem even_mode_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (S : Submodule ℂ (paritySpace D hu s))
    (stable : ∀ (a : FixedCarrier D) (n : ℤ) (v : paritySpace D hu s),
      v ∈ S → (fixedParitySlice D hu s a)[[n]] v ∈ S)
    (a : Carrier D) (ha : theta D a = a) (n : ℤ)
    (x : ActualTensor D hu) (hx : x ∈ lifted D hu s S) :
    (slice D hu a 0)[[n]] x ∈ lifted D hu s S := by
  obtain ⟨v, hv, rfl⟩ := hx
  let source : FixedCarrier D := ⟨a, (mem_fixedSpace D a).mpr ha⟩
  refine ⟨(fixedParitySlice D hu s source)[[n]] v, stable source n v hv, ?_⟩
  change ((fixedParitySlice D hu s source)[[n]] v : ActualTensor D hu) = _
  rw [physicalSlice_mode]
  change (correctedField D hu a).coeff (2*(-n-1)) v =
    (correctedField D hu a).coeff (-2*n-0-2) v
  congr 2
  omega

private theorem odd_mode_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (S : Submodule ℂ (paritySpace D hu s))
    (a : Carrier D) (ha : theta D a = -a) (n : ℤ)
    (x : ActualTensor D hu) (hx : x ∈ lifted D hu s S) :
    (slice D hu a 1)[[n]] x ∈ oddSpan D hu s S :=
  Submodule.subset_span ⟨a, ha, n, x, hx, rfl⟩

private theorem source_product_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (g d : ℤ)
    (ha : theta D a = (-1 : ℂ)^g • a)
    (hb : theta D b = (-1 : ℂ)^d • b)
    (W : Submodule ℂ (ActualTensor D hu)) (x : ActualTensor D hu)
    (iterates : ∀ c : Carrier D, theta D c = (-1 : ℂ)^(g+d) • c →
      ∀ k : ℤ, (slice D hu c (g+d))[[k]] x ∈ W) (m n : ℤ) :
    (slice D hu a g)[[m]] ((slice D hu b d)[[n]] x) ∈ W := by
  apply product_mem_of_iterates _ _ _ g
    (first_eigen_arbitrary_second D hu a g ha b d) W x ?_ m n
  intro r k
  apply iterates (LatticeAllStateReconstruction.mu D a r b) _ k
  simpa only [LatticeAllStateReconstruction.mu,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)] using
    mode_eigenvalue_selection D ((-1 : ℂ)^g) ((-1 : ℂ)^d) a b ha hb r

/-- Monodromy kills the unmatched raw exponents. The matching exponents are
exactly all integer physical modes with lift zero or one. -/
private theorem raw_mem_of_modes (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Carrier D) (g : ℤ) (hg : g = 0 ∨ g = 1)
    (ha : theta D a = (-1 : ℂ)^g • a)
    (W : Submodule ℂ (ActualTensor D hu)) (x : ActualTensor D hu)
    (modes : ∀ n : ℤ, (slice D hu a g)[[n]] x ∈ W) (e : ℤ) :
    (correctedField D hu a).coeff e x ∈ W := by
  have mono : (-1 : ℂ)^g • (correctedField D hu a).coeff e x =
      (-1 : ℂ)^e • (correctedField D hu a).coeff e x := by
    have h := congrArg (fun F => F x) (correctedField_theta D hu a e)
    simpa only [ha, map_smul, Pi.smul_apply, LinearMap.smul_apply] using h
  have vanish (different : (-1 : ℂ)^g ≠ (-1 : ℂ)^e) :
      (correctedField D hu a).coeff e x = 0 := by
    have zero : (((-1 : ℂ)^g)-((-1 : ℂ)^e)) •
        (correctedField D hu a).coeff e x = 0 := by
      rw [sub_smul, mono, sub_self]
    exact (smul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr different)
  rcases hg with rfl | rfl
  · by_cases he : Even e
    · obtain ⟨k, hk⟩ := he
      have member := modes (-k-1)
      rw [physicalSlice_mode] at member
      rw [show -2*(-k-1)-0-2 = e by omega] at member
      exact member
    · rw [vanish (by simp [neg_one_zpow_eq_ite, he])]
      exact W.zero_mem
  · by_cases he : Even e
    · rw [vanish (by simp [neg_one_zpow_eq_ite, he])]
      exact W.zero_mem
    · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
      have member := modes (-k-2)
      rw [physicalSlice_mode] at member
      rw [show -2*(-k-2)-1-2 = e by omega] at member
      exact member

/-- For either sign, every complex submodule of the entire actual parity
space stable under every integer physical mode of every original fixed source
is bottom or top. Zero rank and zero parity spaces remain in scope. -/
theorem fixedParitySlice_irreducible (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (hs : s = 1 ∨ s = -1)
    (S : Submodule ℂ (paritySpace D hu s))
    (stable : ∀ (a : FixedCarrier D) (n : ℤ) (v : paritySpace D hu s),
      v ∈ S → (fixedParitySlice D hu s a)[[n]] v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  let E := lifted D hu s S
  let O := oddSpan D hu s S
  let T := E ⊔ O
  have evenOdd (a b : Carrier D) (ha : theta D a = a) (hb : theta D b = -b)
      (m n : ℤ) (x : ActualTensor D hu) (hx : x ∈ E) :
      (slice D hu a 0)[[m]] ((slice D hu b 1)[[n]] x) ∈ O := by
    apply source_product_mem D hu a b 0 1 (by simpa using ha) (by simpa using hb)
      O x ?_ m n
    intro c hc k
    exact odd_mode_mem D hu s S c (by simpa using hc) k x hx
  have oddOdd (a b : Carrier D) (ha : theta D a = -a) (hb : theta D b = -b)
      (m n : ℤ) (x : ActualTensor D hu) (hx : x ∈ E) :
      (slice D hu a 1)[[m]] ((slice D hu b 1)[[n]] x) ∈ E := by
    apply source_product_mem D hu a b 1 1 (by simpa using ha) (by simpa using hb)
      E x ?_ m n
    intro c hc k
    have member := even_mode_mem D hu s S stable c (by norm_num at hc ⊢; exact hc)
      (k+1) x hx
    -- The original iterate lift is 2, so its k-th mode is fixed lift 0 at k+1.
    simpa only [physicalSlice_mode, show (1:ℤ)+1 = 2 by omega,
      show -2*(k+1)-0-2 = -2*k-2-2 by omega] using member
  have physicalStable (a : Carrier D) (g : ℤ) (hg : g = 0 ∨ g = 1)
      (ha : theta D a = (-1 : ℂ)^g • a) (m : ℤ)
      (x : ActualTensor D hu) (hx : x ∈ T) : (slice D hu a g)[[m]] x ∈ T := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    apply T.add_mem
    · rcases hg with rfl | rfl
      · exact le_sup_left (even_mode_mem D hu s S stable a (by simpa using ha) m y hy)
      · exact le_sup_right (odd_mode_mem D hu s S a (by simpa using ha) m y hy)
    · rcases hg with rfl | rfl
      · have hle : O ≤ O.comap ((slice D hu a 0)[[m]]) := by
          apply Submodule.span_le.mpr
          intro v hv
          obtain ⟨b, hb, n, w, hw, rfl⟩ := hv
          exact evenOdd a b (by simpa using ha) hb m n w hw
        exact le_sup_right (hle hz)
      · have hle : O ≤ E.comap ((slice D hu a 1)[[m]]) := by
          apply Submodule.span_le.mpr
          intro v hv
          obtain ⟨b, hb, n, w, hw, rfl⟩ := hv
          exact oddOdd a b (by simpa using ha) hb m n w hw
        exact le_sup_left (hle hz)
  have fullStable (a : Carrier D) (e : ℤ) (x : ActualTensor D hu) (hx : x ∈ T) :
      (correctedField D hu a).coeff e x ∈ T := by
    have invol : theta D (theta D a) = a := theta_involutive D a
    have plusEigen : theta D (plusPart D a) = plusPart D a := by
      simp only [plusPart, map_smul, map_add, invol]
      module
    have minusEigen : theta D (minusPart D a) = -minusPart D a := by
      simp only [minusPart, map_smul, map_sub, invol]
      module
    have split : a = plusPart D a + minusPart D a := by
      dsimp [plusPart, minusPart]
      module
    have plus := raw_mem_of_modes D hu (plusPart D a) 0 (Or.inl rfl)
      (by simpa using plusEigen) T x
      (fun n => physicalStable _ 0 (Or.inl rfl) (by simpa using plusEigen) n x hx) e
    have minus := raw_mem_of_modes D hu (minusPart D a) 1 (Or.inr rfl)
      (by simpa using minusEigen) T x
      (fun n => physicalStable _ 1 (Or.inr rfl) (by simpa using minusEigen) n x hx) e
    rw [split]
    simpa only [map_add, Pi.add_apply, LinearMap.add_apply] using T.add_mem plus minus
  have opposite : O ≤ paritySpace D hu (-s) := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨b, hb, n, x, hx, rfl⟩ := hv
    apply (mem_parity D hu (-s) _).mpr
    rw [physicalSlice_mode, correctedField_target_parity, hb,
      lifted_parity D hu s S x hx]
    simp [map_smul, smul_neg]
  by_cases bottom : S = ⊥
  · exact Or.inl bottom
  right
  have Tnonzero : T ≠ ⊥ := by
    intro hT
    apply bottom
    apply bot_unique
    intro v hv
    have inT : (v : ActualTensor D hu) ∈ T :=
      le_sup_left (show (v : ActualTensor D hu) ∈ E from ⟨v, hv, rfl⟩)
    rw [hT, Submodule.mem_bot] at inT
    exact Subtype.ext inT
  have Ttop : T = ⊤ :=
    (ActualFieldIrreducible.correctedField_irreducible D hu T fullStable).resolve_left Tnonzero
  apply top_unique
  intro v hv
  have inT : (v : ActualTensor D hu) ∈ T := by rw [Ttop]; trivial
  obtain ⟨y, hy, z, hz, sum⟩ := Submodule.mem_sup.mp inT
  have yp := lifted_parity D hu s S y hy
  have zp := (mem_parity D hu (-s) z).mp (opposite hz)
  have vp := (mem_parity D hu s v).mp v.property
  have relation := congrArg (actualParity D hu) sum
  rw [map_add, yp, zp, vp, ← sum, smul_add] at relation
  have zzero : z = 0 := by
    have twice : (2*s) • z = 0 := by
      have subtract : (-s) • z = s • z := add_left_cancel relation
      calc
        (2*s) • z = s • z - (-s) • z := by module
        _ = 0 := sub_eq_zero.mpr subtract.symm
    exact (smul_eq_zero.mp twice).resolve_left (by rcases hs with rfl | rfl <;> norm_num)
  obtain ⟨u, huS, huY⟩ := hy
  have yv : y = (v : ActualTensor D hu) := by simpa only [zzero, add_zero] using sum
  have uv : u = v := Subtype.ext (huY.trans yv)
  exact uv ▸ huS

end D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible
