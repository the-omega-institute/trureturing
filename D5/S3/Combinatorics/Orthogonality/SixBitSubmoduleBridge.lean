/- GID: D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SixBitLineTransfer.result; instance=D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.bits_dot
   digest: Exact XOR/coordinate, finite-space/submodule and orthogonality graph equivalences. -/

import D5.S3.Combinatorics.Orthogonality.SixBitCatalogue
import D5.S3.Combinatorics.Orthogonality.NikandishClique
import Mathlib.Algebra.Module.TransferInstance

set_option autoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.Orthogonality.SixBitSubmoduleBridge

abbrev Mask := BinaryOrthogonality.Vector
abbrev Coordinates := Fin 6 → ZMod 2

/-- Coordinate i is exactly low bit i of the supplied integer representation. -/
def bits (v : Mask) : Coordinates := fun i => (v.val / 2 ^ i.val % 2 : ℕ)

private theorem bits_bijective : Function.Bijective bits := by decide +kernel
theorem bits_zero : bits 0 = 0 := by decide +kernel
private theorem bits_add : ∀ x y : Mask,
    bits (BinaryOrthogonality.add x y) = bits x + bits y := by decide +kernel
theorem bits_dot : ∀ x y : Mask,
    dotProduct (bits x) (bits y) = 0 ↔ BinaryOrthogonality.dot x y = 0 := by
  decide +kernel

noncomputable def bitsEquiv : Mask ≃ Coordinates := Equiv.ofBijective bits bits_bijective

/-- A wrapper gives the source's masks their binary vector-space operations,
not the unrelated arithmetic-modulo-64 operations on Fin 64. -/
structure BinaryVector where
  mask : Mask
  deriving DecidableEq, Fintype

noncomputable def vectorEquiv : BinaryVector ≃ Coordinates :=
  (show BinaryVector ≃ Mask from
    ⟨BinaryVector.mask, BinaryVector.mk, fun _ => rfl, fun _ => rfl⟩).trans bitsEquiv

noncomputable instance : AddCommGroup BinaryVector := vectorEquiv.addCommGroup
noncomputable def vectorAddEquiv : BinaryVector ≃+ Coordinates :=
  { vectorEquiv with map_add' := fun _ _ => vectorEquiv.apply_symm_apply _ }
noncomputable instance : Module (ZMod 2) BinaryVector := vectorAddEquiv.module (ZMod 2)
noncomputable def vectorLinearEquiv : BinaryVector ≃ₗ[ZMod 2] Coordinates :=
  vectorAddEquiv.linearEquiv (ZMod 2)

/-- Image of a specified complete XOR-closed finite space. -/
def toSubmodule (U : Finset Mask) (hU : BinaryOrthogonality.IsSpace U) :
    Submodule (ZMod 2) Coordinates where
  carrier := bits '' (U : Set Mask)
  zero_mem' := ⟨0, hU.1, bits_zero⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨BinaryOrthogonality.add x y, hU.2 x hx y hy, bits_add x y⟩
  smul_mem' := by
    intro c x hx
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases hc with rfl | rfl
    · simpa only [zero_smul] using (show (0 : Coordinates) ∈ bits '' (U : Set Mask) from
        ⟨0, hU.1, bits_zero⟩)
    · simpa only [one_smul] using hx

private theorem mem_toSubmodule (U : Finset Mask) (hU : BinaryOrthogonality.IsSpace U)
    (v : Mask) : bits v ∈ toSubmodule U hU ↔ v ∈ U := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact bits_bijective.1 he ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private noncomputable def fromSubmodule (P : Submodule (ZMod 2) Coordinates) : Finset Mask := by
  classical
  exact Finset.univ.filter (fun v => bits v ∈ P)

private theorem from_isSpace (P : Submodule (ZMod 2) Coordinates) :
    BinaryOrthogonality.IsSpace (fromSubmodule P) := by
  constructor
  · simp [fromSubmodule, bits_zero]
  · intro x hx y hy
    simp only [fromSubmodule, Finset.mem_filter, Finset.mem_univ, true_and] at *
    rw [bits_add]
    exact P.add_mem hx hy

/-- The complete source lattice and the actual coordinate-submodule lattice
are equivalent. Every submodule is present; no catalogue completeness is
assumed by this representation bridge. -/
noncomputable def spaceEquiv :
    {U : Finset Mask // BinaryOrthogonality.IsSpace U} ≃
      Submodule (ZMod 2) Coordinates where
  toFun U := toSubmodule U.1 U.2
  invFun P := ⟨fromSubmodule P, from_isSpace P⟩
  left_inv U := by
    apply Subtype.ext
    ext v
    simp [fromSubmodule, mem_toSubmodule]
  right_inv P := by
    ext x
    obtain ⟨v, rfl⟩ := bits_bijective.2 x
    simp [mem_toSubmodule, fromSubmodule]

private theorem zero_space_iff (U : Finset Mask) (hU : BinaryOrthogonality.IsSpace U) :
    toSubmodule U hU = ⊥ ↔ U = {0} := by
  constructor
  · intro he
    apply Finset.ext
    intro v
    constructor
    · intro hv
      have hz : bits v = 0 := by
        have hm := (mem_toSubmodule U hU v).mpr hv
        rw [he] at hm
        exact hm
      have hv0 := bits_bijective.1 (hz.trans bits_zero.symm)
      exact Finset.mem_singleton.mpr hv0
    · intro hv
      exact (Finset.mem_singleton.mp hv).symm ▸ hU.1
  · intro he
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [he] at hv
      simpa only [Finset.mem_singleton.mp hv, bits_zero, Submodule.mem_bot]
    · intro hx
      have hx0 : x = 0 := hx
      exact ⟨0, hU.1, bits_zero.trans hx0.symm⟩

/-- All nonzero source spaces, including the whole space, correspond to all
nonzero actual Submodules. Source zero is precisely the singleton mask {0}. -/
noncomputable def vertexEquiv : BinaryOrthogonality.Vertex ≃ NikandishClique.Vertex 6 := by
  let f : BinaryOrthogonality.Vertex → NikandishClique.Vertex 6 := fun U =>
    ⟨toSubmodule U.1 U.2.1, fun h => U.2.2 ((zero_space_iff U.1 U.2.1).mp h)⟩
  apply Equiv.ofBijective f
  constructor
  · intro U W h
    apply Subtype.ext
    have he : toSubmodule U.1 U.2.1 = toSubmodule W.1 W.2.1 :=
      congrArg Subtype.val h
    have hs : (⟨U.1, U.2.1⟩ : {S : Finset Mask // BinaryOrthogonality.IsSpace S}) =
        ⟨W.1, W.2.1⟩ := spaceEquiv.injective he
    exact congrArg (fun S : {S : Finset Mask // BinaryOrthogonality.IsSpace S} => S.1) hs
  · intro P
    obtain ⟨U, hU⟩ := spaceEquiv.surjective P.1
    have hn : U.1 ≠ {0} := by
      intro he
      apply P.2
      rw [← hU]
      exact (zero_space_iff U.1 U.2).mpr he
    exact ⟨⟨U.1, U.2, hn⟩, Subtype.ext hU⟩

/-- The graph isomorphism transfers the supplied full positive certificate
with its native-evaluation dependencies unchanged. -/
noncomputable def graphIso : BinaryOrthogonality.graph ≃g NikandishClique.orthogonalityGraph 6 where
  toEquiv := vertexEquiv
  map_rel_iff' := by
    intro U W
    change (vertexEquiv U ≠ vertexEquiv W ∧ _) ↔ (U ≠ W ∧ _)
    rw [vertexEquiv.injective.ne_iff]
    apply and_congr_right
    intro _
    constructor
    · intro h u hu w hw
      exact (bits_dot u w).mp (h (bits u) ⟨u, hu, rfl⟩ (bits w) ⟨w, hw, rfl⟩)
    · intro h u hu w hw
      obtain ⟨v, hv, rfl⟩ := hu
      obtain ⟨z, hz, rfl⟩ := hw
      exact (bits_dot v z).mpr (h v hv z hz)

#print axioms graphIso

end D5.S3.Combinatorics.Orthogonality.SixBitSubmoduleBridge
