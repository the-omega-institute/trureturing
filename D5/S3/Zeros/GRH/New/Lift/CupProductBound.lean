/- GID: D5/S3/Zeros/GRH/New/Lift/CupProductBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/CupProductBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.CupProductBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/CupProductBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.BlochKato.BlochKato
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cokernel bounds and vanishing cup products for Kisin modules (see New.Lift.LongGap).

This file: a cup product of crystalline cocycles is a coboundary if they have lifts to
W(C^♭)-coefficients whose Galois and Frobenius differences pair into W(𝔪^♭). -/

noncomputable section

namespace Lift

open KummerChart Topology crysCocycles FrobGroup Submodule IsLocallyConstant Finset
variable {p} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] {O}

/-- One side of a pairing: a lattice datum Y (`Lift.KummerChart.JumpLattice`) with 0 in every jump
set U_i, a lattice C, and an O-linear map α: C → Z_f(Y), the crystalline cocycles. -/
structure KummerChart.PairingSide (O : Coeffs) extends kerLattice :
  JumpLattice O where (C : GalLattice O Γ) (α : C →ₗ[O] crysCocycles ρ) zero_mem i : 0 ∈ U i

variable {k} (S S' : PairingSide O)

/-- For a side S, the lattice datum formed by the extension of the trivial lattice C by Y given
by the cocycles of S, with ζ and the jump sets of S. -/
abbrev KummerChart.PairingSide.extLattice := JumpLattice.mk ⟨_,
  extensionRep S.α⟩ S.U _ ⟨isAdmissible_extensionRep _ S.inClass.1, fun _ _ n ↦ by
  simpa [or_iff_not_imp_left] using S.inClass.2.1 _ _ ∘ ne_bot_of_le_ne_bot n ∘ jump_extension_le
    _, nofun⟩ (insert_subset (S.zero_mem _) <| S.embJumps_subset ·)

/-- For a side S, the lattice datum formed by C with trivial action of Γ, with ζ and jump set
{0} at every letter. -/
abbrev KummerChart.PairingSide.trivLattice : JumpLattice O :=
  ⟨⟨S.C, 1⟩, fun _ ↦ {0}, _, .of_cyclotomic_pow 0, by simp⟩

/-- The projection from the extension of C by Y onto the trivial lattice C, as an equivariant
map of lattice data. -/
abbrev KummerChart.PairingSide.projTriv : S.extLattice.Hom S.trivLattice := ⟨.snd .., by tauto⟩

/-- For a side S with extension Ỹ = Y ⊕ C, the W(C^♭)-linear map W(C^♭) ⊗ Ỹ → W(C^♭) ⊗ Y induced
by the projection to the first summand. -/
abbrev KummerChart.PairingSide.wittFst := S.extLattice.wittMap S.kerLattice (.fst ..)

/-- For two sides S, S', the lattice datum Y ⊗_O Y' with the element ζ and, at each letter i,
the sumset U(i) + U'(i) of their integer sets. -/
abbrev KummerChart.PairingSide.tensorLattice := JumpLattice.mk _ (fun i ↦ (S.U i).image₂ (· + ·)
  (S'.U i)) _ (S.inClass.tensor S'.inClass) (by grw [S.embJumps_subset ·, S'.embJumps_subset ‹_›])

variable {S S' e} (P : Pairing S.toGalLattice S'.toGalLattice) (n : FrobGroup Γ)

/-- The side defined by a pairing P of Y and L: the lattice (Y ⊗ L)^∨(1), C = O with trivial
action, α(o) = o·c for the cocycle c of P, and jump sets holding 0 and the −u − u' − 1. -/
abbrev Pairing.thirdSide : PairingSide O := let T := S.tensorLattice S'; ⟨⟨_, fun i ↦
    insert 0 ((T.U i).image (-· - 1)), _, T.inClass.dual, (by grind [T.embJumps_subset ·])⟩, ⟨O, 1⟩,
    .toSpanSingleton _ _ P.thirdClass, by simp⟩

/-- The W(C^♭)-bilinear extension of the pairing Y×L→Z/p^m(1) to a pairing of W(C^♭)⊗Y and
W(C^♭)⊗L with values in W(C^♭)⊗Z/p^m(1). -/
abbrev Pairing.wittPairing :=
  (DiagTensor.pair P.modPairing : S.Ambient →ₗ[_] S'.Ambient →ₗ[_] DiagTensor (.of (charRep _ χ)))

/-- The pair (w, y) is safe: p^e times the pairing of the components of w, y in W(C^♭) ⊗ Y,
W(C^♭) ⊗ L lies in the image of W(𝔪^♭). -/
def Pairing.IsSafe e w y := p ^ e • P.wittPairing (S.wittFst w) (S'.wittFst y) ∈ smallPart _

/-- The cup product under P of α(c) and p^e α'(c') is a continuous coboundary
(`Lift.Pairing.CupBounds`) for every topology on Γ making j = `Γ.overGp.toGp` an open embedding. -/
def Pairing.ScaledCupBounds e c c' := ∀ ⦃_ : TopologicalSpace Γ⦄, IsOpenEmbedding Γ.overGp.toGp →
  P.CupBounds (S.α c) (p ^ e • S'.α c')

lemma wittFst_smul : ∀ x, S.wittFst (n • x) =
  n • S.wittFst x + S.trivLattice.wittMap S.kerLattice (.fst .. ∘ₗ extensionRep S.α (snd n) ∘ₗ
  .inr ..) (n • S.projTriv.wittMap x) := diagTensor_induction (by simp; simp [extensionRep])
    (by simp +contextual <;> grind -abstractProof)

lemma Pairing.smul_wittPairing x y : n • P.wittPairing x y = P.wittPairing (n • x) (n • y) :=
  .symm (baseChangePairing_map _ (P.modPairing_rho _) ..)

attribute [local simp] smul_sub smul_smul MonoidHom.map_one Pairing.smul_wittPairing wittFst_smul
  extensionRep
attribute [-simp] _root_.map_smul LinearMap.map_smul_of_tower map_one nsmul_eq_mul

/-- Let e₁ + e₂ + e₃ ≤ e, let x, w lie over p^{e₁}c and x' over p^{e₂}c'. If ((g−1)x, g(h−1)x'),
(w−x, (g−1)x'), ((g−1)w, g(φ−1)x'), (φx−w, (g−1)φx') satisfy `Lift.Pairing.IsSafe` e₃ for all g,
h in Γ', then `Lift.Pairing.ScaledCupBounds` holds for e, c, c'. -/
lemma Pairing.ScaledCupBounds.of_isSafe {e₁ e₂ e₃ c c'} x w x' (he : e₁ + e₂ + e₃ ≤ e) (hx :
  S.projTriv.wittMap x = p ^ e₁ • .mk 1 c) (hw : S.projTriv.wittMap w = p ^ e₁ • .mk 1 c) (hx' :
  S'.projTriv.wittMap x' = p ^ e₂ • .mk 1 c') (H : ∀ g : k.galMonoid, (∀ h :
  k.galMonoid, P.IsSafe e₃ (g • x - x) (g • (h • x' - x'))) ∧ P.IsSafe e₃ (w - x) (g • x' - x') ∧
  P.IsSafe e₃ (g • w - w) (g • (φ • x' - x')) ∧ P.IsSafe e₃ (φ • x - w) (g • φ • x' - φ • x')) :
  P.ScaledCupBounds e c c' := by
  intro _ hj; let B y := p ^ e₃ • P.wittPairing (S.wittFst y)
  have V {T : PairingSide O} {c} h := eventually_eq_pow_smul T.inClass.isPotCrys (c := c) h P.m
  obtain ⟨⟨z, h₀, C⟩, ⟨r, o⟩, u, _, Z, X, _⟩ := TateTwist.smallPart_spec (V <|
    coboundary_mem ·) (B x), pow_dvd_pow p he, nearOne_le, isLocalGalois_localFieldOf hj,
    apply_mul (S.α c).2, apply_mul (S'.α c').2, @smul_comm.{0,0,0} (FrobGroup Γ)
  choose y hd using (z (B w (S'.wittFst (φ • x' - x')))).2.1
  have N := (V (S'.α c').2).and ((V (S.α c).2).and
    ((C (S'.wittFst x')).and ((TateTwist.smallPart_spec (Quot.ind fun c ↦
    (eventually_eq_pow_smul (isAdmissible_of_cyclotomicGp_zpow 1 (ρ := charRep ..) (by simp; tauto))
    (coboundary_mem c) _).mono fun _ ⟨w, h⟩ ↦ ⟨w, congr($h)⟩) .id).2.2 y)))
  rw [nearOne_eq_nhds_one hj] at *
  choose κ hκ using fun g : k.Γ' ↦ let n := inr g.1
    (z (B (n • x) (n • S'.wittFst x') - n • (B x (S'.wittFst x') - y) - B x
      (S'.wittFst (n • x' - x')) - y)).2.2 (by
    convert (H ⟨_, g, rfl⟩).2.symm.elim (sub_mem <| ·.elim sub_mem) using 1
    linear_combination (norm := (simp +zetaDelta [*, (phi_mul_comm _).eq]; abel)) hd - n • hd)
  have key (g h : k.Γ') := congrArg (zmodPowToUnits _) (sub_eq_zero.1 (h₀ (p ^ e • P.modPairing
    ((S.α c).1 g) (S'.ρ g ((S'.α c').1 h)) - r • (charRep _ χ g.1 (κ h) - κ (g * h) + κ g)) (by
    convert nsmul_mem (add_mem ((H ⟨_, g, rfl⟩).1 ⟨_, h, rfl⟩) (add_mem (sub_mem
      (smul_mem_smallPart g.1 (hκ h)) (hκ (g * h))) (hκ g))) r
    simp +zetaDelta [*, -h₀, pow_add, mul_comm]; abel)))
  refine mem_comap.1 <| (ker_mkQ _).le <| (nsmul_eq_zero_iff_of_coprime (index_coprime.pow_right
    _)).1 ⟨((unitsModule _).restrictAlong ⟨toGp, hj.continuous⟩).index_smul_eq_zero_of_resH2 ⟨_,
    k.Γ'.isOpen_of_mem_nhds (u (·.2))⟩ (x := ⟦⟨_, ((iff_eventually_eq _).2 fun q ↦
    map_mul_left_nhds_one q ▸ ((N.and (V (coboundary_mem ((S'.α c').1 q.2)))
    ).prod_nhds N).mono (by rintro ⟨⟩ ⟨⟨⟨-, ⟨⟨⟩⟩⟩, _, e⟩, ⟨⟨⟩⟩⟩; simp [*, -h₀, eq_add_of_sub_eq e,
    ↓nsmul_quot_eq_zero])).continuous, by simp [map_cyclotomicGp_smul _ nsmul_zmodPowToUnits, Z, X,
    modPairing_rho, Units.smul_def]⟩⟧) ((ker_mkQ _).ge ⟨zmodPowToUnits _ ∘ (r • κ),
    (isLocallyConstant_of_eventually_mul (.mono (continuousAt_subtype_val N) ?_)).continuous,
    by simpa [map_cyclotomicGp_smul _ nsmul_zmodPowToUnits, charRep] using!
    key⟩), congr(⟦⟨fun _ ↦ $(nsmul_zmodPowToUnits _), _⟩⟧)⟩
  rintro h ⟨⟨⟩, ⟨⟩, e₁, e₀⟩ _
  simpa [*, -h₀, ↓nsmul_quot_eq_zero, eq_neg_add_iff_add_eq, h₀ _ (by
    convert sub_mem (sub_mem e₀ e₁) (hκ h); simp +zetaDelta [*, -smul_smul]; abel)] using key _ h
