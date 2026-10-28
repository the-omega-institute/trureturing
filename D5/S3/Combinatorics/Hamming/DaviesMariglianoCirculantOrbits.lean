/- GID: D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.claim; result=D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.result; claim=D5/S3/Combinatorics/Hamming/DaviesMariglianoCirculantOrbits.claim
   digest: A thirty-vertex circulant has more pair orbits than distinct eigenvalues. -/

/-
result:
  proof_shape: bind-only (finite certificates and library transport, with helpers inlined)
  escape_witness: none
  admission_basis: open-problem-resolution (#21260; Refuted)
  Direct frozen dependencies: none
All private theorem helpers are bind-only and consumed by result through the dependency chain.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The claim retains the preregistered expressions; proofs use Mathlib commonNeighbors and
Matrix.circulant directly, with the finite adjacency correspondence checked below.
Diagonal unordered pairs and the full graph automorphism group are retained.
The bounds eight or more pair orbits and seven or fewer eigenvalues suffice; exact counts
and infinite-family extensions are not asserted here. Literature completeness is
ASSUMED-UNVERIFIED: the Beezer originals remain unread (issue #21260).
-/

import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Basic.Real.Basic

namespace D5.S3.Combinatorics.Hamming.DaviesMariglianoCirculantOrbits

/-- A symmetry that is a cyclic permutation of all vertices. -/
def IsCirculant {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  0 < n ∧ ∃ σ : G ≃g G, Equiv.Perm.IsCycleOn σ.toEquiv Set.univ

/-- Orbits of the entrywise action on V*V, including s(v,v). -/
def pairOrbits {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Set (Sym2 (Fin n))) :=
  Set.range (fun p : Sym2 (Fin n) => Set.range (fun σ : G ≃g G => Sym2.map σ p))

/-- Number of distinct real adjacency eigenvalues. -/
noncomputable def eigenvalueCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Nat.card (Module.End.Eigenvalues (G.adjMatrix ℝ).mulVecLin)

/-- Conjecture 4.4: every uncoloured circulant graph has equally many unordered-pair
orbits (under the full automorphism group) and distinct adjacency eigenvalues. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    IsCirculant G → Nat.card (pairOrbits G) = eigenvalueCount G

end D5.S3.Combinatorics.Hamming.DaviesMariglianoCirculantOrbits

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.Hamming.DaviesMariglianoCirculantOrbits

private def baseGraph : SimpleGraph (Fin 30) where
  Adj x y :=
    (x.val % 2 ≠ y.val % 2 ∧ x.val % 3 = y.val % 3 ∧ x.val % 5 = y.val % 5) ∨
    (x.val % 2 = y.val % 2 ∧ x.val % 3 ≠ y.val % 3 ∧ x.val % 5 = y.val % 5) ∨
    (x.val % 2 = y.val % 2 ∧ x.val % 3 = y.val % 3 ∧ x.val % 5 ≠ y.val % 5)
  symm := ⟨by intro x y h; aesop⟩
  loopless := ⟨by intro x; simp⟩

private instance baseGraphDecidable : DecidableRel baseGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

private def edgeAvoid (c : ℕ) (x y : Fin 30) : Prop :=
  baseGraph.Adj x y ∧ (baseGraph.commonNeighbors x y).toFinset.card ≠ c
private instance edgeAvoidDecidable (c : ℕ) : DecidableRel (edgeAvoid c) := by intro x y; unfold edgeAvoid; infer_instance

private def coordRel (c : ℕ) (x y : Fin 30) : Prop :=
  x = y ∨ edgeAvoid c x y ∨ ∃ z, edgeAvoid c x z ∧ edgeAvoid c z y

private theorem shift_adj : ∀ x y : Fin 30,
    baseGraph.Adj (finRotate 30 x) (finRotate 30 y) ↔ baseGraph.Adj x y := by
  decide

private def shift : baseGraph ≃g baseGraph where
  toEquiv := finRotate 30
  map_rel_iff' := shift_adj _ _

private theorem base_circulant : IsCirculant baseGraph := by
  refine ⟨by decide, shift, ?_⟩
  change (finRotate 30).IsCycleOn Set.univ
  simpa [support_finRotate] using
    (isCycle_finRotate (n := 28)).isCycleOn


private theorem common_map (σ : baseGraph ≃g baseGraph) (x y : Fin 30) :
    (baseGraph.commonNeighbors (σ x) (σ y)).toFinset.card = (baseGraph.commonNeighbors x y).toFinset.card := by
  symm
  apply Finset.card_equiv σ.toEquiv
  intro z
  simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
  exact (and_congr σ.map_rel_iff σ.map_rel_iff).symm

private theorem avoid_map (σ : baseGraph ≃g baseGraph) (c : ℕ) (x y : Fin 30) :
    edgeAvoid c (σ x) (σ y) ↔ edgeAvoid c x y := by
  simp only [edgeAvoid, common_map, σ.map_rel_iff]

private theorem coord_map (σ : baseGraph ≃g baseGraph) (c : ℕ) (x y : Fin 30) :
    coordRel c (σ x) (σ y) ↔ coordRel c x y := by
  simp only [coordRel, σ.injective.eq_iff, avoid_map]
  constructor
  · rintro (h | h | ⟨z, hx, hy⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨w, rfl⟩ := σ.surjective z
      exact Or.inr (Or.inr ⟨w, (avoid_map σ c x w).mp hx,
        (avoid_map σ c w y).mp hy⟩)
  · rintro (h | h | ⟨z, hx, hy⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨σ z, (avoid_map σ c x z).mpr hx,
        (avoid_map σ c z y).mpr hy⟩)

private theorem avoid_two : ∀ x y : Fin 30,
    edgeAvoid 0 x y ↔ baseGraph.Adj x y ∧ x.val % 2 = y.val % 2 := by decide
private theorem avoid_three : ∀ x y : Fin 30,
    edgeAvoid 1 x y ↔ baseGraph.Adj x y ∧ x.val % 3 = y.val % 3 := by decide
private theorem avoid_five : ∀ x y : Fin 30,
    edgeAvoid 3 x y ↔ baseGraph.Adj x y ∧ x.val % 5 = y.val % 5 := by decide

private theorem coord_two : ∀ x y : Fin 30,
    coordRel 0 x y ↔ x.val % 2 = y.val % 2 := by
  simpa only [coordRel, avoid_two] using
    (show ∀ x y : Fin 30,
      (x = y ∨ (baseGraph.Adj x y ∧ x.val % 2 = y.val % 2) ∨
        ∃ z, (baseGraph.Adj x z ∧ x.val % 2 = z.val % 2) ∧
          (baseGraph.Adj z y ∧ z.val % 2 = y.val % 2)) ↔
        x.val % 2 = y.val % 2 from by decide)
private theorem coord_three : ∀ x y : Fin 30,
    coordRel 1 x y ↔ x.val % 3 = y.val % 3 := by
  simpa only [coordRel, avoid_three] using
    (show ∀ x y : Fin 30,
      (x = y ∨ (baseGraph.Adj x y ∧ x.val % 3 = y.val % 3) ∨
        ∃ z, (baseGraph.Adj x z ∧ x.val % 3 = z.val % 3) ∧
          (baseGraph.Adj z y ∧ z.val % 3 = y.val % 3)) ↔
        x.val % 3 = y.val % 3 from by decide)
private theorem coord_five : ∀ x y : Fin 30,
    coordRel 3 x y ↔ x.val % 5 = y.val % 5 := by
  simpa only [coordRel, avoid_five] using
    (show ∀ x y : Fin 30,
      (x = y ∨ (baseGraph.Adj x y ∧ x.val % 5 = y.val % 5) ∨
        ∃ z, (baseGraph.Adj x z ∧ x.val % 5 = z.val % 5) ∧
          (baseGraph.Adj z y ∧ z.val % 5 = y.val % 5)) ↔
        x.val % 5 = y.val % 5 from by decide)

private theorem mod_map (σ : baseGraph ≃g baseGraph) (x y : Fin 30) :
    ((σ x).val % 2 = (σ y).val % 2 ↔ x.val % 2 = y.val % 2) ∧
    ((σ x).val % 3 = (σ y).val % 3 ↔ x.val % 3 = y.val % 3) ∧
    ((σ x).val % 5 = (σ y).val % 5 ↔ x.val % 5 = y.val % 5) := by
  exact ⟨(coord_two _ _).symm.trans ((coord_map σ 0 x y).trans (coord_two _ _)),
    (coord_three _ _).symm.trans ((coord_map σ 1 x y).trans (coord_three _ _)),
    (coord_five _ _).symm.trans ((coord_map σ 3 x y).trans (coord_five _ _))⟩


private def tag (x y : Fin 30) : ℕ :=
  (if x.val % 2 = y.val % 2 then 0 else 1) +
  (if x.val % 3 = y.val % 3 then 0 else 2) +
  (if x.val % 5 = y.val % 5 then 0 else 4)

private def pairTag : Sym2 (Fin 30) → ℕ :=
  Sym2.lift ⟨tag, by intro x y; simp only [tag, eq_comm]⟩

private theorem pairTag_map (σ : baseGraph ≃g baseGraph) (p : Sym2 (Fin 30)) :
    pairTag (Sym2.map σ p) = pairTag p := by
  induction p using Sym2.inductionOn with
  | _ x y =>
    simp only [Sym2.map_mk, pairTag, Sym2.lift_mk, tag,
      (mod_map σ x y).1, (mod_map σ x y).2.1, (mod_map σ x y).2.2]

private def representative (i : Fin 8) : Fin 30 := ![0,15,10,25,6,21,16,1] i

private theorem representative_tag : ∀ i : Fin 8,
    pairTag s(0, representative i) = i.val := by decide

private theorem orbit_lower : 8 ≤ Nat.card (pairOrbits baseGraph) := by
  classical
  let f : Fin 8 → pairOrbits baseGraph := fun i =>
    ⟨Set.range (fun σ : baseGraph ≃g baseGraph => Sym2.map σ s(0, representative i)),
      ⟨s(0, representative i), rfl⟩⟩
  have hfinite : (pairOrbits baseGraph).Finite := Set.finite_range _
  let : Finite (pairOrbits baseGraph) := hfinite.to_subtype
  have hf : Function.Injective f := by
    intro i j hij
    have hm : s(0, representative i) ∈ (f i).val :=
      ⟨RelIso.refl baseGraph.Adj, rfl⟩
    rw [hij] at hm
    obtain ⟨σ, hσ⟩ := hm
    apply Fin.ext
    calc
      i.val = pairTag s(0, representative i) := (representative_tag i).symm
      _ = pairTag (Sym2.map σ s(0, representative j)) := congrArg pairTag hσ.symm
      _ = pairTag s(0, representative j) := pairTag_map σ _
      _ = j.val := representative_tag j
  simpa using Nat.card_le_card_of_injective f hf

open Matrix

private def certVec0 : Fin 30 → ℤ := ![0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,1,0,0,1,0,1,0,0,0,1,0,0,0,0,0]

private theorem intMatrix_adj : ∀ x y,
    Matrix.circulant certVec0 x y = baseGraph.adjMatrix ℤ x y := by
  have h : ∀ x y : Fin 30,
      certVec0 (x - y) = (if baseGraph.Adj x y then (1 : ℤ) else 0) := by decide
  intro x y
  exact h x y

private def certVec1 : Fin 30 → ℤ := ![7,0,2,2,2,2,-4,0,2,2,-6,0,-4,0,2,-7,2,0,-4,0,-6,2,2,0,-4,2,2,2,2,0]

private theorem cert_step0 :
    (Matrix.circulant certVec0) *ᵥ certVec0 - (7 : ℤ) • certVec0 = certVec1 := by decide

private def certVec2 : Fin 30 → ℤ := ![-70,6,-12,-15,-12,-21,21,6,-12,-15,41,6,21,6,-12,54,-12,6,21,6,41,-15,-12,6,21,-21,-12,-15,-12,6]

private theorem cert_step1 :
    (Matrix.circulant certVec0) *ᵥ certVec1 - (5 : ℤ) • certVec1 = certVec2 := by decide

private def certVec3 : Fin 30 → ℤ := ![500,-48,68,102,68,182,-130,-48,68,102,-262,-48,-130,-48,68,-388,68,-48,-130,-48,-262,102,68,-48,-130,182,68,102,68,-48]

private theorem cert_step2 :
    (Matrix.circulant certVec0) *ᵥ certVec2 - (4 : ℤ) • certVec2 = certVec3 := by decide

private def certVec4 : Fin 30 → ℤ := ![-2432,256,-304,-512,-304,-1024,608,256,-304,-512,1216,256,608,256,-304,2048,-304,256,608,256,1216,-512,-304,256,608,-1024,-304,-512,-304,256]

private theorem cert_step3 :
    (Matrix.circulant certVec0) *ᵥ certVec3 - (2 : ℤ) • certVec3 = certVec4 := by decide

private def certVec5 : Fin 30 → ℤ := ![4480,-560,560,1120,560,2240,-1120,-560,560,1120,-2240,-560,-1120,-560,560,-4480,560,-560,-1120,-560,-2240,1120,560,-560,-1120,2240,560,1120,560,-560]

private theorem cert_step4 :
    (Matrix.circulant certVec0) *ᵥ certVec4 - (-1 : ℤ) • certVec4 = certVec5 := by decide

private def certVec6 : Fin 30 → ℤ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

private theorem cert_step5 :
    (Matrix.circulant certVec0) *ᵥ certVec5 - (-3 : ℤ) • certVec5 = certVec6 := by decide

private theorem cert_final : certVec6 = 0 := by
  exact List.ofFn_inj.mp rfl

private theorem cert_matrix_step {v w : Fin 30 → ℤ} {c : ℤ}
    (h : (Matrix.circulant certVec0) *ᵥ v - c • v = w) :
    ((Matrix.circulant certVec0) - c • 1) * Matrix.circulant v = Matrix.circulant w := by
  rw [sub_mul, Matrix.circulant_mul, smul_mul_assoc, one_mul,
    ← Matrix.circulant_smul, ← Matrix.circulant_sub]
  exact congrArg Matrix.circulant h

private theorem annihilator_int :
    ((Matrix.circulant certVec0) + 3) * (((Matrix.circulant certVec0) + 1) * (((Matrix.circulant certVec0) - 2) *
      (((Matrix.circulant certVec0) - 4) * (((Matrix.circulant certVec0) - 5) * (((Matrix.circulant certVec0) - 7) * (Matrix.circulant certVec0)))))) = 0 := by
  have h0 := cert_matrix_step cert_step0
  have h1 := cert_matrix_step cert_step1
  have h2 := cert_matrix_step cert_step2
  have h3 := cert_matrix_step cert_step3
  have h4 := cert_matrix_step cert_step4
  have h5 := cert_matrix_step cert_step5
  norm_num only [Int.reduceNeg, neg_smul, one_smul, neg_neg, sub_neg_eq_add,
    zsmul_one, Int.cast_ofNat, Int.cast_neg, Int.cast_one] at h0 h1 h2 h3 h4 h5
  change _ * (_ * (_ * (_ * (_ * (_ * Matrix.circulant certVec0))))) = _
  rw [h0, h1, h2, h3, h4, h5, cert_final, Matrix.circulant_zero]

private theorem intMatrix_real :
    (Int.castRingHom ℝ).mapMatrix (Matrix.circulant certVec0) = baseGraph.adjMatrix ℝ := by
  ext x y
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, intMatrix_adj,
    SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

open Polynomial in
private noncomputable def annihilator : ℝ[X] :=
  (X + C 3) * ((X + C 1) * ((X - C 2) *
    ((X - C 4) * ((X - C 5) * ((X - C 7) * X)))))

private theorem annihilator_zero :
    Polynomial.aeval (baseGraph.adjMatrix ℝ).mulVecLin annihilator = 0 := by
  have hr := congrArg ((Int.castRingHom ℝ).mapMatrix) annihilator_int
  simp only [map_mul, map_add, map_sub, map_ofNat, map_one, map_zero, intMatrix_real] at hr
  have hl := congrArg (Matrix.toLinAlgEquiv' : Matrix (Fin 30) (Fin 30) ℝ ≃ₐ[ℝ] _) hr
  have heq : Matrix.toLinAlgEquiv' (baseGraph.adjMatrix ℝ) =
      (baseGraph.adjMatrix ℝ).mulVecLin := by
    exact Matrix.toLin'_apply' _
  simpa only [annihilator, map_mul, map_add, map_sub, heq, Polynomial.aeval_X,
    Polynomial.aeval_C, map_ofNat, map_one, map_zero] using hl

private theorem eigenvalue_mem (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (baseGraph.adjMatrix ℝ).mulVecLin μ) :
    μ ∈ ({-3,-1,0,2,4,5,7} : Finset ℝ) := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h := Module.End.aeval_apply_of_hasEigenvector (p := annihilator) hv
  rw [annihilator_zero, LinearMap.zero_apply] at h
  have hp : annihilator.eval μ = 0 := (smul_eq_zero.mp h.symm).resolve_right hv.2
  simpa only [annihilator, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero,
    sub_eq_zero, add_eq_zero_iff_eq_neg, Finset.mem_insert, Finset.mem_singleton,
    or_assoc, or_comm, or_left_comm] using hp

private theorem eigenvalue_upper : eigenvalueCount baseGraph ≤ 7 := by
  classical
  let E := Module.End.Eigenvalues (baseGraph.adjMatrix ℝ).mulVecLin
  let T : Finset ℝ := {-3,-1,0,2,4,5,7}
  let f : E → T := fun μ => ⟨μ.val, eigenvalue_mem μ.val μ.property⟩
  have hf : Function.Injective f :=
    Function.Injective.of_comp (f := fun z : T => z.val)
      (Subtype.val_injective : Function.Injective (fun μ : E => μ.val))
  have ht : Nat.card T = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    norm_num [T]
  have hdec : (fun a b : Fin 30 => Classical.propDecidable (baseGraph.Adj a b)) =
      baseGraphDecidable := Subsingleton.elim _ _
  unfold eigenvalueCount
  rw [hdec]
  exact (Nat.card_le_card_of_injective f hf).trans ht.le


theorem result : ¬ claim := by
  intro h
  have heq := h 30 baseGraph base_circulant
  have ho := orbit_lower
  have he := eigenvalue_upper
  omega

end D5.S3.Combinatorics.Hamming.DaviesMariglianoCirculantOrbits
