/- GID: D5/S3/Zeros/GRH/New/Lift/LongGap
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/LongGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.LongGap. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/LongGap.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Lift.CokernelKillers
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Cokernel bounds and vanishing cup products for Kisin modules. Explicit powers of p
(ℓ in the Selmer bound) and of the
Eisenstein polynomial kill cokernels of Kisin modules on crystalline extensions, Galois operators
give divisibility at a known cost, and a walk along Frobenius orbits makes cup products of
crystalline classes vanish up to powers of ℓ; these tools bound the loss above ℓ in the Selmer
bound. Zero cokernel for weights of one sign, cup products via Ext, and torsion bounds by Sen
operators are known. Related work: Čoupek–Gazaki–Marmora, Exactness property of Breuil–Kisin
functors and Bloch–Kato Selmer groups, 2026; Gao–Liu, Integral Sen theory and integral Hodge
filtration, 2024; Chang–Diamond, Extensions of rank one (φ,Γ)-modules and crystalline
representations, 2011.

Part of: Length bound for crystalline classes with few low weights (see New.Lift.ExponentTheorems).

This file: Points, strictness, safe pairs and the walk along Frobenius orbits killing cup products.
Gap step: an explicit power kills cup products absent small negative weights. Long gap lemma: a deep
point from one coefficient of the E-expansion. -/

open Algebra Finset IsDiscreteValuationRing LinearMap Module Polynomial Submodule Lift.Pairing
  Lift.KummerChart.JumpLattice

/-- The lattice datum O(1), on which Γ acts through the cyclotomic character, with jump set {−1}
at every letter (`Lift.KummerChart.Letter`, a unit of the field with p^f elements). -/
noncomputable abbrev Lift.KummerChart.tateLattice {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {k :
  KummerChart Γ} O :
  JumpLattice O := ⟨⟨O, actionRep O O χ⟩, fun _ ↦ {-1}, _, .of_cyclotomic_pow 1 (by simp), by simp⟩

namespace Lift.KummerChart.PairingSide

attribute [-simp] Equiv.Perm.coe_inv map_mul map_one smul_right_inj

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {S S' :
  PairingSide O} {c : S.C} {i : Letter} (S : PairingSide O) (i : Letter) (S' : PairingSide O) (c' :
  S.C) (i' : Letter) (e : ℕ) (o₁ o' : ℕ → ℤ → ℤ)

lemma stepBack_zero (i : Letter) : i.stepBack 0 = i := rfl

/-- The inclusion of Y into the extension of C by Y, as an equivariant map of lattice data. -/
abbrev inclKer : S.Hom S.extLattice := ⟨.inl .., by aesop (add simp extensionRep)⟩

/-- The Z_p-linear map from `Lift.KummerChart.JumpLattice.kisinLoc` of the extension of C by Y to
W(C^♭) ⊗ C induced by the projection onto C. -/
noncomputable abbrev projTrivLoc :=
  S.projTriv.wittMap.restrictScalars ℤ_[p] ∘ₗ S.extLattice.kisinLoc.subtype.restrictScalars _

/-- The Z_p-module of x in 𝒩 (`Lift.KummerChart.JumpLattice.kisinLoc`) of the extension that lie
over a constant at i and are deep for o: gx − x ∈ `Lift.KummerChart.JumpLattice.withExponents` i o
for g in Γ'. -/
noncomputable def deepElements o := (S.constantAt i).range.comap S.projTrivLoc ⊓ (invariantsMod
  (S.extLattice.withExponents i o)).comap (S.extLattice.kisinLoc.subtype.restrictScalars _)

/-- The A_inf-submodule of elements of W(C^♭) ⊗ Ỹ, Ỹ the extension of S, with exponents o at the
letter i (`Lift.KummerChart.JumpLattice.withExponents`) that map to 0 in W(C^♭) ⊗ C. -/
noncomputable def kerWithExponents o :=
  S.extLattice.withExponents i o ⊓ (S.projTriv.wittMap.restrictScalars _).ker

/-- The additive endomorphism A of 𝒩 has cost e: for all i, o and x in
`Lift.KummerChart.PairingSide.deepElements` i o, Ax − p^e x lies in
`Lift.KummerChart.PairingSide.kerWithExponents` i o. -/
def Reaches (e : ℕ) (A : S.extLattice.kisinLoc →+ S.extLattice.kisinLoc) := ∀ ⦃i o x⦄,
  x ∈ S.deepElements i o → A x - p ^ e • x ∈ locKisinPart (S.kerWithExponents i o)

/-- The type of pairings (`Lift.Pairing`) between the lattices Y and Y' of the sides S and S'. -/
abbrev SidePairing := Pairing S.toGalLattice S'.toGalLattice

/-- x lies in `Lift.KummerChart.JumpLattice.kisinLoc` of the extension, maps to p^e times the
letter-i part of 1⊗c, has exponents o, and all gx − x (g ∈ Γ') have exponents o'. -/
def pointsOver := {x ∈ S.extLattice.kisinLoc | S.projTriv.wittMap x = p ^ e • S.constantAt i' c' ∧
  x ∈ S.extLattice.withExponents i' o₁ ∧ x ∈ invariantsMod (S.extLattice.withExponents i' o')}

/-- Condition on S at letter i: a point over p^e c, exponents o(i), depth d, with z + d +
min(−v, o') > 0 on all lines; a cut σ^{−r}i; if Q, o(i) ≥ `Lift.KummerChart.stdExponent` l and φ^r z
+ d + min(o', φ^l o') > 0. -/
def HasDeepPoint (cut : _ → Prop) l (o o' z : _ → ℕ → ℤ → ℤ) (Q : Prop) := ∃ d r,
    (S.pointsOver c' i' e (o i') d).Nonempty ∧ cut (i'.stepBack r) ∧ ∀ a, ∀ u ∈ S.U (i'.stepBack a),
  ∀ v ∈ S'.U (i'.stepBack a), -z i' a (-u - v - 1) - d a u < min (-v) (o' i' a v) ∧
  (Q → stdExponent l a u ≤ o i' a u ∧ -frobExponent r 0 (z (i'.stepBack r)) a (-u - v - 1) - d a u <
  min (o' i' a v) (frobExponent l 0 (o' (i'.stepBack l)) a v))

variable {S S' : PairingSide O} {c : S.C} {i : Letter} {c' :
  S'.C} {l κ s e e' : ℕ} {o} {o' o₁ : ℕ → ℤ → ℤ} {o₂ o₃ x w y} {P : S.SidePairing S'} {n} (hK :
  n ∈ P.thirdSide.pointsOver 1 (i.stepBack l) κ o₂ o₃ ∧ ∀ a, Antitone (o₂ a)) (hx :
  x ∈ S.pointsOver c i e o₁ o) (hw : w ∈ S.kerWithExponents i o) (hy :
  y ∈ S'.kerWithExponents i o') (H : ∀ a, ∀ u ∈ S.U (i.stepBack a), ∀ u' ∈ S'.U (i.stepBack a), 0 <
  frobExponent l 0 o₂ a (-u - u' - 1) + o a u + o' a u') (g : galMonoid) (I : Finset ((_ : ℕ) × ℤ))

@[simp] lemma wittFst_inclKer : ∀ y, wittFst _ (S.inclKer.wittMap y) = y ∧
  S.projTriv.wittMap (S.inclKer.wittMap y) = 0 := diagTensor_induction (by simp)

lemma isSafe_sum {u v : _ → _} (h : ∀ i, u i ∈ S.extLattice.letterPart i ∧
  v i ∈ S'.extLattice.letterPart i)
  (f : ∀ i, P.IsSafe κ (u i) (v i)) : P.IsSafe κ (∑ i, u i) (∑ i, v i) := by
  have Z i := Fintype.sum_eq_single i fun l n ↦ show P.wittPairing (wittFst _ (u l))
    (wittFst _ (v i)) = 0 from (isUnit_teichmuller_sub (Units.ext.mt n)).smul_eq_zero.1
    (by simpa [by simpa [mem_letterPart_iff_mulZeta] using h, sub_smul] using!
    (diagTensor_induction fun _ _ ↦ diagTensor_induction (by simp [mulZeta, modPairing]) : ∀ u v,
    P.wittPairing (wittFst _ (S.extLattice.mulZeta.wittMap u)) (wittFst _ v) =
    P.wittPairing (wittFst _ u) (wittFst _ (S'.extLattice.mulZeta.wittMap v))) (u l) (v i))
  simp_all [IsSafe, smul_sum, sum_mem]

/-- An invariant functional μ on Y with μ(1 ⊗ Y) in a B_dR^+-submodule W of B_dR extends to an
invariant functional on the extension of C by Y that maps the A_inf-span of the lattice into
W. -/
lemma exists_extend_form (W : Submodule BdRPlus _) {μ} (h : μ ∈ S.forms) (m : ∀ t,
  μ (.mk 1 t) ∈ W) : ∃ ν ∈ S.extLattice.forms, S.extLattice.ainfLattice ≤
  (W.restrictScalars _).comap ν ∧ ν ∘ₗ S.inclKer.wittMap = μ := by
  let Λ := (μ.restrictScalars _ ∘ₗ DiagTensor.mk 1).liftBaseChange Bcris
  have H (g : k.Γ') y : Λ (tensorAction _ (toGp g.1) (S.ρ g) y) = toGp g.1 • Λ y := by
    induction y <;> simp_all [Λ, tensorAction, h _, smul_def']
  choose v F using (S.α · |>.2)
  have f c (g : k.Γ') := by simpa [↓H, Λ] using congr(Λ $(F c g))
  choose a b d using fun c ↦ by simpa using BdR.exists_sub_mem_of_smul_sub_mem k.Γ' W (f c · ▸ m _)
  let e := finBasis ℤ_[p] S.C
  let ⟨ν, q⟩ :=
    S.trivLattice.exists_functional_extend (e.constr ℕ ((Λ ∘ v - algebraMap _ _ ∘ a) ∘ e))
  use μ ∘ₗ ↑S.wittFst + ν ∘ₗ S.projTriv.wittMap, fun (t, c) g ↦ ?_, span_le.2 ?_, LinearMap.ext
    (diagTensor_induction ?_) <;> simp [Λ, sum_mem, smul_of_tower_mem, add_mem_cancel_left, *]
  rw [← e.sum_repr c]
  simp [*, extensionRep, -Basis.sum_repr, smul_sum, smul_sub, smul_comm, h t, add_assoc]

lemma Reaches.mem_of_stable {A P x} (H : S.Reaches e A) (l : locKisinPart (S.kerWithExponents i o) ≤
  P) (m : x ∈ P) (y : x ∈ S.deepElements i o) :
  A x ∈ P := (sub_mem_iff_left _ (nsmul_mem m _)).1 (l (H y))

lemma kerWithExponents_le_deepElements : locKisinPart (S.kerWithExponents i o) ≤
  S.deepElements i o := fun _ m ↦ ⟨ker_le_comap _ m.2, smul_sub_mem_withExponents m.1⟩

/-- Strictness: a vector w of the extension with exponents o at the letter i and image 0 in
W(C^♭) ⊗ C comes from a vector y of the sublattice with exponents o, and y lies in 𝒩 if w
does. -/
lemma exists_inclKer_eq_of_projTriv_eq_zero (hw : w ∈ S.kerWithExponents i o) : ∃ y ∈
  S.withExponents i o, S.inclKer.wittMap y = w ∧ (w ∈ S.extLattice.kisinLoc → y ∈ S.kisinLoc) := by
  obtain ⟨y, rfl⟩ : w ∈ S.inclKer.wittMap.range :=
    (lTensor_exact _ .inl_snd snd_surjective _).1 hw.2
  have l := mem_letterPart_iff_letterProj.2
    (by simpa [← Hom.wittMap_letterProj]
    using congr(wittFst _ $(mem_letterPart_iff_letterProj.1 hw.1.1.2)))
  use y, ⟨⟨?y, l⟩, fun a u hu μ hμ ↦ ?_⟩, rfl, fun m ↦
    (wittFst_inclKer y).1 ▸ coordRetract_of_mem_kisinLoc m hw.1.1.1 ▸ S.inclKer.map_coordRetract
    ⟨y, ?y⟩ ⟨_, _⟩ rfl ▸ by simp
  exact hw.1.1.1.imp fun _ ↦ .imp_right (.imp (.imp fun _ ↦ .imp_right (by
    simpa using wittMap_mem_ainfLattice (.fst ..) ·)) fun e a μ m ↦
    (exists_extend_form ⊤ m (by simp)).elim (by simp_all [eq_comm]))
  obtain ⟨ν, e, f, g⟩ := exists_extend_form _ (comp_letterProj_mem_forms hμ.1) hμ.2
  simpa [↓← valueAt_comp_wittMap, JumpLattice.valueAt, mem_letterPart_iff_letterProj.1,
    ← phi_pow_smul_mem_letterPart_iff, *] using hw.1.2 a u hu ν ⟨e,
    (f <| letterProj_mk_mem_ainfLattice ·)⟩

/-- If p^κ E^s kills the cokernel at the letter i (`Lift.KummerChart.PairingSide.KillsCokernel`),
then for each c in C there is a point over p^κ c whose exponents and depth are −u − s at E and −u at
φ^a E, a ≥ 1. -/
lemma pointsOver_nonempty_of_killsCokernel (hK : S.KillsCokernel i κ s) c : (S.pointsOver c i κ
  (raisedAtE (-s)) (raisedAtE (-s))).Nonempty := have ⟨x, ⟨m, t⟩, e⟩ :=
    (exists_lift_of_mem_liftIdeal hK).choose_spec _ (constantAt_mem_locLetterPart c)
  ⟨_, frobEUnit_zpow_smul_mem_kisinLoc.2
    m, by simp [e, inv_smul_eq_iff, frobEUnit_pow_smul, frobE_eq]; module,
    frobEUnit_zpow_mem_withExponents 0 (-s) t,
    smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents _ _ t)⟩

/-- For a finite set I of steps (a, n) there is an additive map A on 𝒩, of cost the sum of
v_p(n) + d + 3a (`cost`, d = `differentExp`) over I, raising depth c to depth c' whenever I
contains all (a, n) with
c_a(u) ≤ n < c'_a(u), u an allowed jump. -/
lemma exists_reaches_deep : ∃ A, S.Reaches (∑ q ∈ I, cost q.1 q.2) A ∧ ∀ ⦃i c x⦄, x ∈ S.deepElements
  i c → ∀ c', (∀ a, ∀ u ∈ S.U (i.stepBack a), ∀ n, c a u ≤ n → n < c' a u → ⟨a, n⟩ ∈ I) → A x ∈
  S.deepElements i c' := I.induction_on_max_value (·.2) ⟨.id _, by simp [Reaches], fun _ _ _ m _ J ↦
  m.imp_right fun m g ↦ mem_withExponents_of_le (m g) (by simp_all)⟩ fun ⟨a, n⟩ I q N ⟨A, R, Y⟩ ↦ by
  obtain ⟨_, t, υ, Z⟩ := S.extLattice.exists_reaches_depth_succ a n
  let B := p ^ cost a n • .id _ + ∑ l, AddMonoidHom.mk' (S.extLattice.coordRetract <|
    υ • ⟨_, smul_sub_mem_zTau_kisinLocAinf (t l) ·.2⟩) (by simp [← map_add, add_sub_add_comm])
  have T : S.Reaches (cost a n) B := fun i c x ⟨⟨_, f⟩, m⟩ ↦ by
    simp [B] at f ⊢
    exact sum_mem fun l _ ↦ ⟨coordRetract_mem_withExponents _ (smul_mem _ υ
      (smul_sub_mem_zTauUnit_smul_of_deep x.2 (m _))), by simp [S.projTriv.map_coordRetract _ 0,
      ← f, constantAt, gal_smul_letterProj, k.galMonoid.smul_def]⟩
  refine ⟨B.comp A, fun i c x m ↦
    (sub_mem_iff_left _ (T (R.mem_of_stable kerWithExponents_le_deepElements m m))).1 (by
    simp [← smul_sub, R m, q, pow_add, mul_smul, nsmul_mem]), fun i c x m d J ↦ ?_⟩
  have Y := Y m (fun b u ↦ ite (b = a ∧ d b u = n + 1) n (d b u))
    (have := (J · · · (n + 1)); by clear * - this J N q; grind)
  refine (T.mem_of_stable kerWithExponents_le_deepElements Y Y).imp_right fun H g ↦
    mem_withExponents_of_mem_hodgeFil (H g) fun b u v l μ m ↦ ?_
  obtain ⟨y : (A x).1 ∈ invariantsMod _, rfl, e⟩ := Y.2, (ite_ne_right_iff.1 l.ne).1
  obtain ⟨c, f⟩ := Z _ (A x).2 μ m.1 (BdR.exists_sub_mem_of_smul_sub_mem _ _ (by
    simpa [e, ↓valueAt_smul_sub (A x).2.1 m.1] using! y ⟨_, ·, rfl⟩ |>.2 _ u v μ m))
  have F := valueAt_coordRetract_sub_mem_hodgeFil m.1 (p ^ _ • ⟨_, (A x).2.1⟩ + ∑ l,
    υ • ⟨_, smul_sub_mem_zTau_kisinLocAinf (t l) (A x).2⟩) ((valueField _).1.2 c) (by simpa using f)
  erw [e, valueAt_smul_sub (B _).2.1 m.1]
  simpa [B, coordRetract_of_mem_kisinLoc, nsmul_mem, smul_sub, galMonoid_smul_localFieldOf] using
    sub_mem (galMonoid_smul_mem_hodgeFil g F) F

include hx in
/-- A point over p^e c with exponents o₁ and depth o gives a point over p^{e'} c of depth o'
with exponents `Lift.KummerChart.JumpLattice.improvedExponent`, if I contains all steps from o to o'
and e' ≥ e + the total cost of I. -/
lemma pointsOver_nonempty_of_costs (H : ∀ a, ∀ u ∈ S.U (i.stepBack a), ∀ n, o a u ≤ n → n < o' a u →
  ⟨a, n⟩ ∈ I) (he : e + ∑ n ∈ I, cost n.1 n.2 ≤ e') :
  (S.pointsOver c i e' (improvedExponent o₁ o') o').Nonempty := by
  obtain ⟨⟨s, rfl⟩, A, R, D⟩ := he.dest, S.exists_reaches_deep I
  have y {o} H : p ^ s • ⟨x, hx.1⟩ ∈ S.deepElements i o :=
    smul_of_tower_mem _ _ ⟨⟨p ^ e • c, by simp [hx.2]⟩, H⟩
  obtain ⟨z, -, D⟩ := y (smul_sub_mem_withExponents hx.2.2.1), D (y hx.2.2.2) o' H
  exact ⟨A _, (A _).2, (sub_mem_ker_iff.1 (R z).2).trans (by simp [hx.2]; module),
    mem_withExponents_of_deep (R.mem_of_stable (P := locKisinPart (withExponents ..)) (fun _ ↦
    (·.1)) (nsmul_mem hx.2.2.1 _) z) D, D⟩

lemma smul_sub_mem_kerWithExponents (hx : x ∈ S.pointsOver c i e o₁ o) (g : galMonoid) :
  k.zTauUnit⁻¹ • (g • x - x) ∈ S.kerWithExponents i o :=
  ⟨JumpLattice.smul_sub_mem_zTauUnit_smul_of_deep hx.1 (hx.2.2.2 g), by simp [k.galMonoid.smul_def,
  hx.2, smul_comm, constantAt, gal_smul_letterProj]⟩

lemma sub_mem_kerWithExponents_of_pointsOver (hx : x ∈ S.pointsOver c i e o₁ o) (hw :
  w ∈ S.pointsOver c i e o₂ o₃) : w - x ∈ S.kerWithExponents i (o₁ ⊓ o₂) :=
  ⟨sub_mem (mem_withExponents_of_le hw.2.2.1 (by simp))
  (mem_withExponents_of_le hx.2.2.1 (by simp)), by simp_all [pointsOver]⟩

lemma phi_pow_smul_mem_pointsOver (hw : w ∈ S.pointsOver c (i.stepBack l) e o o') :
  FrobGroup.φ ^ l • w ∈ S.pointsOver c i e (frobExponent l 0 o) (frobExponent l 1 o') :=
  ⟨phi_pow_mem_kisinLoc hw.1, by simp [hw.2.1, smul_comm, phi_pow_smul_constantAt,
  Equiv.Perm.coe_inv], phi_pow_mem_withExponents hw.2.2.1,
  fun g ↦ have Y := phi_pow_mem_withExponents (smul_sub_mem_kerWithExponents hw g).1
  Eq.subst (by simp [← frobGroup_smul_smul, ← zTauUnit_smul, smul_sub, smul_phi_pow_comm])
    (mem_withExponents_of_mem_hodgeFil (smul_mem _ (FrobGroup.φ ^ l • k.zTau) Y)
    fun a u v c μ e ↦ have c : a < l := by lia
    by simpa [c, zTau] using mul_mem_hodgeFil (phiInvToBdR_mem_hodgeFil_one_iff.2
      ((frobE_dvd_phi_pow_tau c).mul_right _)) (Y.2 a u v μ e))⟩

lemma wittPairing_constantAt_and_thirdPairing
  i : letI B := JumpLattice.wittPairing (C := S.kerLattice) (.lsmul O _); (∀ w,
    B (P.thirdSide.constantAt i 1) w = S.letterProj i w) ∧ ∀ n w y, DiagTensor.map (mkQ _ ∘ₗ P.toZp)
    (JumpLattice.wittPairing (C := tateLattice O) P.thirdPairing n (JumpLattice.wittPairing (C :=
    S.tensorLattice S') (TensorProduct.mk ..) w y)) = P.wittPairing (B ((projTriv _).wittMap n) w)
    y := ⟨diagTensor_induction (by simp [constantAt, wittPairing_letterProj_left]),
  diagTensor_induction fun _ _ ↦ diagTensor_induction fun _ _ ↦ diagTensor_induction
  (by simp [thirdPairing, modPairing,
  mul_assoc, -nsmul_eq_mul]; simp [← map_nsmul, ↓nsmul_quot_eq_zero])⟩

include hK hw hy H in
/-- For paired sides let w, y lie over 0 with exponents o, o' at i, and let the third side have
at σ^{−l}i a point over p^κ with antitone exponents o₂. If o(a,u) + o'(a,u') + [a ≥
l]·o₂(a−l, −u−u'−1) > 0 for all jumps, then (zτw, y), (w, zτy) are safe for κ
(`Lift.Pairing.IsSafe`; zτ is the unit `zTauUnit`). -/
lemma SidePairing.isSafe_of_exponents : IsSafe P κ (zTauUnit • w) y ∧
  IsSafe P κ w (zTauUnit • y) := by
  obtain ⟨⟨w, a, ⟨⟨⟩⟩⟩, ⟨⟨-, N, M⟩, A⟩, y, b, ⟨⟨⟩⟩⟩ := exists_inclKer_eq_of_projTriv_eq_zero hw,
    hK.imp phi_pow_smul_mem_pointsOver (· <| · - l), exists_inclKer_eq_of_projTriv_eq_zero hy
  refine (by simpa [smul_comm _ k.zTauUnit, mem_letterPart_iff_letterProj.1 a.1.2,
    wittPairing_constantAt_and_thirdPairing i, N, IsSafe, smul_smul, -nsmul_eq_mul]
    using! ·) (mem_span.1 ((tateLattice O).tau_pow_smul_mem_ainfLattice_of_chi 1 ((S.tensorLattice
    S').wittPairing_mem_withExponents P.thirdPairing_equivariant M.1 (wittPairing_mem_withExponents
    (b := TensorProduct.mk ..) (c'' := fun a v ↦ 1 - frobExponent l 0 o₂ a (-v - 1)) (by simp) a
    b ?_) ?_)) (comap (k.z.1 • (DiagTensor.map (mkQ _ ∘ₗ P.toZp)).restrictScalars _)
    (smallPart P.m)) fun _ ⟨t, e⟩ ↦ e ▸ ⟨_, smul_of_tower_mem _ (P.toZp t)
    (teichmuller_mem_wittMaxIdeal (k.chart.4 <| k.seriesMap_X ▸ ·.map _)), by
    simp [k.z_eq_teichmuller, mul_smul, ← map_smul, smul_def', smul_comm]⟩)
  all_goals
    clear * - A H; intro a u _ t _ v
    obtain _ := @A a (-v - 1), @A a u; grind

include hK hx hy H in
/-- Under the hypotheses of `Lift.KummerChart.PairingSide.SidePairing.isSafe_of_exponents` on the
point of the third side, on y and on o, o': if x is a point of S at i with all gx − x of exponents
o, then (gx − x, gy) is safe for κ, for every g in Γ'. -/
lemma SidePairing.isSafe_smul_sub : P.IsSafe κ (g • x - x) (g • y) := by simpa using
  (P.isSafe_of_exponents hK (smul_sub_mem_kerWithExponents hx g) (add_mem
  ⟨smul_sub_mem_withExponents hy.1 g, by simp_all [kerWithExponents, k.galMonoid.smul_def]⟩ hy) H).1

/-- The walk. For paired sides, let σ^{−l(i)}i be the nearest cut before i. At each cut let the
three sides have points over p^e c, p^{e'}c', p^κ, the third with antitone exponents, one
side leading, with the stated inequalities. Then `Lift.Pairing.ScaledCupBounds` holds for E
≥ e + e' + κ. -/
lemma SidePairing.scaledCupBounds_of_points_at_cuts (cut Q : _ → Prop) (l :
  k.Letter → ℕ) {o o' z z' : _ → _} (hl : ∀ i, IsLeast {a | 0 < a ∧ cut (i.stepBack a)} (l i)) (H :
  ∀ i, cut i → S.HasDeepPoint S' c i e cut (l i) o o' z (Q i) ∧ S'.HasDeepPoint S c' i e' cut (l i)
  o' o z (¬Q i) ∧ (P.thirdSide.pointsOver 1 i κ (z i) (z' i)).Nonempty
  ∧ ∀ a, Antitone (z i a)) {E} (he : e + e' + κ ≤ E := by omega) : P.ScaledCupBounds E c c' := by
  simp only [HasDeepPoint, Set.Nonempty, and_assoc, ← exists_and_right, ← exists_and_left] at H
  choose! v _ r' x' _ r x a s f b t f' K using H
  let d P i := ite ((P ⊓ cut) i) 0 (l i)
  have q i : (∀ P, cut (i.stepBack (d P i))) ∧ d ⊥ i = d ⊤ (k.letterFrob⁻¹ i) + 1 := by
    have z a : (k.letterFrob⁻¹ i).stepBack a = i.stepBack (a + 1) := rfl
    clear * - hl z; simp [d, IsLeast, lowerBounds, -pow_ite] at *
    grind [z (l i - 1), z 0, stepBack_zero]
  let u {L : JumpLattice O} (y : _ → L.Ambient) P := ∑ i,
    FrobGroup.φ ^ d P i • y (i.stepBack (d P i))
  have B i l a h : (Letter.stepBack i l).stepBack (a - l) =
    _ := congr($(pow_mul_pow_sub k.letterFrob h)⁻¹ i)
  replace a P i := phi_pow_smul_mem_pointsOver (a _ ((q i).1 P))
  replace b P i := phi_pow_smul_mem_pointsOver (b _ ((q i).1 P))
  have Y := by simpa [pointsOver, withExponents] using And.intro a b
  have F L y : FrobGroup.φ • @u L y ⊤ = u y ⊥ := by
    rw [smul_sum, ← Equiv.sum_comp k.letterFrob⁻¹]; simp [u, q, pow_succ', mul_smul]
  refine .of_isSafe _ (u x ⊤) (u x Q) (u x' ⊤) he ?_ ?_ ?_ fun g ↦ ⟨fun h ↦ ?_, ?_, ?_, ?_⟩ <;>
    simp only [↓F, u, smul_sum, ← sum_sub_distrib]
  iterate 3 simp [Y, ← smul_sum, constantAt, sum_letterProj]
  all_goals refine isSafe_sum (by simp [sub_mem, gal_smul_mem_letterPart, Y]) fun i ↦ have c :=
      (hl i).1.2
    have G {j} m := P.isSafe_smul_sub (K (.stepBack i j) m) (a Q i)
      (sub_mem_kerWithExponents_of_pointsOver (b ⊤ i) (b ⊥ i))
    have T {j} m U V W H :=
      (P.isSafe_of_exponents (K (.stepBack i j) m) (sub_mem_kerWithExponents_of_pointsOver (a U i)
      (a V i)) (smul_sub_mem_kerWithExponents (b W i) g) H).2; ?_
  apply P.isSafe_smul_sub (K _ ((q i).1 ⊤)) (a ..) ⟨smul_sub_mem_withExponents (b ..).2.2.1
    h, by simpa [inv_smul_eq_iff] using (smul_sub_mem_kerWithExponents (b ⊤ i) h).2⟩
  clear * - B f q; grind
  all_goals by_cases hi : cut i <;> by_cases n : Q i <;> try simp [d, IsSafe, *]; done
  map_tacs [convert T (t i hi) ⊤ Q ⊤ _; apply G (s i hi); apply G c; convert T c Q ⊥ ⊥ _]
  all_goals clear * - f f' B c hi n; simp [d, *] <;> grind

variable (h : S.SidePairing S') {a κ η H W : ℕ} {b : Letter → ℕ} {ε : Letter → ℤˣ} {i : Letter} {c :
  S.C}

/-- If p divides no nonzero integer within n of 0, ±b, and all steps from depth o to hi occur at
E in this range, a point over p^κ c with exponents lo gives one over p^{κ+(8n+4)d} c of
depth hi, exponents `Lift.KummerChart.JumpLattice.improvedExponent`. -/
lemma pointsOver_nonempty_of_noMultipleNear {lo o n b} (hx : (S.pointsOver c i κ lo o).Nonempty)
  (hs : NoMultipleNear p n b) hi (H : ∀ a, ∀ u ∈ S.U (i.stepBack a), ∀ y, o a u ≤ y → y < hi a u →
  a = 0 ∧ y ∈ twoWindows n b ∪ twoWindows n (-b)) : (S.pointsOver c i (κ + (8 * n + 4) *
  differentExp) (improvedExponent lo hi) hi).Nonempty := pointsOver_nonempty_of_costs hx.some_mem
  (.image (.mk 0) (twoWindows n b ∪ twoWindows n (-b))) (by grind) (by
    grw [sum_le_card_nsmul _ _ k.differentExp, card_image_le]; repeat grw [card_union_le]
    all_goals grind [cost, NoMultipleNear, padicValInt.eq_zero_iff, Int.card_Icc])

/-- Paired sides, jump sets in opposite windows, p^κE^a kills for the three extensions, no non-zero
multiple of p within 6(a+η+W) of 0, ±b_i. Let the sets miss [−a, 0), or: unramified, p ≥ 5, η ≥ 1,
second sets in [−η, 0]. Then `Lift.Pairing.ScaledCupBounds` holds with any exponent
H ≥ 3(κ + (48(a+η+W)+4)d), d = `differentExp`.

Rank-free exponents for crystalline classes at large weights. -/
lemma SidePairing.scaledCupBounds_of_killsCokernel (hK : ∀ i, h.thirdSide.KillsCokernel i κ a ∧
  S.KillsCokernel i κ a ∧ S'.KillsCokernel i κ a) (hs : ∀ i, NoMultipleNear p (6 * (a + η + W)) (b
  i)) (hU : ∀ i, IsInJumpWindow η (-ε i) (b i) W (S.U i) ∧ IsInJumpWindow η (ε i) (b i) W (S'.U i))
  (h₀ : (∀ i u, u ∈ S.U i ∨ u ∈ S'.U i → u ∉ Ico (-↑a) 0) ∨ IsUnramified ∧ 5 ≤ p ∧ 1 ≤ η ∧ ∀ i,
  S'.U i ⊆ .Icc (-η) 0) (hH : 3 * (κ + (8 * (6 * (a + η + W)) + 4) * differentExp) ≤ H) c c' :
  h.ScaledCupBounds H c c' := by
  let D := raisedAtE (2 * a + η)
  obtain t | ⟨hk, hp, t⟩ := h₀
  have y i := pointsOver_nonempty_of_noMultipleNear
    (pointsOver_nonempty_of_killsCokernel (hK i).2.2 c') (hs i) D ?_
  let l := 0; rotate_right; let l := 1
  have y i := pointsOver_nonempty_of_noMultipleNear (i := i) ⟨_, phi_pow_smul_mem_pointsOver
    (l := 1) (pointsOver_nonempty_of_noMultipleNear (pointsOver_nonempty_of_killsCokernel
    (killsCokernel_of_isUnramified 0 0 ?_ hk hp) c') (hs i) D ?_).some_mem⟩ (hs i) (D ·.pred) ?_
  any_goals refine h.scaledCupBounds_of_points_at_cuts ⊤ (ε · = 1 ∧ l = 0) 1 (by
    simp; tauto) fun i _ ↦ ⟨⟨_, 0, pointsOver_nonempty_of_noMultipleNear
    (pointsOver_nonempty_of_killsCokernel (hK i).2.1 c) (hs i) D ?_, ⟨⟩, ?_⟩,
    ⟨_, ite (ε i = 1) l 0, y i, ⟨⟩, ?_⟩, pointsOver_nonempty_of_killsCokernel (hK i).1 1, ?_⟩
  all_goals clear * - t hU; rintro ⟨⟩ <;> simp +zetaDelta [Antitone, ← Units.val_eq_one,
    raisedAtE] <;> intros <;> and_intros <;> grind

end Lift.KummerChart.PairingSide

namespace Lift.KummerChart.JumpLattice

attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule

/-- The system of exponents obtained from o by raising the single value o(a, u) by 1. -/
@[grind] def raiseExponent (o : ℕ → ℤ → ℤ) a u b v := o b v + ite (b = a ∧ v = u) 1 0

seal Finset.univ Finset.sum Finset.prod in
/-- Unramified chart: if u has multiplicity ≤ n at the letter b steps before l and o_b(u) <
o_b(v) for jumps v < u, any fn+1 elements of 𝒩 with exponents o have a ℤ_p-combination, one
coefficient 1, in the sum of the `locKisinPart`s of `withExponents` l (o + 1 at E) and of
`withExponents` l (`raiseExponent` o b u). -/
lemma exists_comb_of_jumpMultiplicity_le {p} [ThePrime p] [Γ : GroupOverGp p] {k :
  KummerChart Γ} {O} {L : JumpLattice O} o (hk : IsUnramified) {i u n} (hn :
  L.jumpMultiplicity i u ≤ n) b l (f : .stepBack l b = i) (ho : ∀ v ∈ L.U i, v < u → o b u < o b v)
  (x : Fin (k.f * n + 1) → kisinLoc) (X : ∀ j, ↑(x j) ∈ L.withExponents l o) : ∃ᵉ (c :
  _ → ℤ_[p]) (j), c j = 1 ∧ ∑ j, c j • x j ∈ locKisinPart (L.withExponents l fun a v ↦
  o a v + ite (0 = a) 1 0) ⊔ locKisinPart (withExponents l (raiseExponent o b u)) := by
  obtain ⟨⟨r, q, ν, R⟩, rfl⟩ := exists_span_formsOfType_mod_pred i u, f
  choose t ht using fun l m ↦ mem_hodgeFil (n :=
    o b u).1 (valueAt_mem_of_hodgeFil_le _ (X l) (ν m).2)
  -- Auerbach: all the leading terms are integral combinations of at most `r` of them
  let U := (Matrix.of (thetaBdR <| t · ·)).toLin'.range
  choose s z H B using exists_auerbach (finBasis _ U) (.proj · ∘ₗ U.subtype)
    (by bound) (.id _) fun _ ↦ continuous_bot
  choose A hA using fun l m ↦ theta_surjective ⟨(z m).1 l, by simpa using B l m⟩
  choose w y hw using fun l m ↦ by simpa [Chart.frobE, Fin.exists_fin_succ_pi] using
    (k.exists_dvd_sub_sum_z_pow 0 (by simp [hk.2] : _ = 1) (k.coord₀ (FrobGroup.φ ^ b • A l m)))
  have S r := sum_smul_mem _ r (t := univ) fun m _ ↦ X (s m)
  -- a relation among the `W`-parts of the coefficients, divided by its entry of least valuation
  obtain ⟨a, e, n⟩ := Fintype.not_linearIndependent_iff.1 (mt (·.fintype_card_le_finrank (b := w)
    (R := ℤ_[p])) (by simp [finrank_wittFq]
                      grw [finrank_range_le, finrank_fin_fun, q, hn, mul_comm]))
  choose l c g using by simpa [addVal_le_iff_dvd] using Finite.exists_min (addVal _ ∘ a)
  rw [_root_.funext g] at e n; simp [mul_smul, ← smul_sum, funext_iff] at e n
  refine ⟨c, l, by simpa [n] using g l,
    Eq.subst (by ext; simp [-sum_add_distrib, coordRetract_of_mem_kisinLoc, smul_sum, ← hw,
    coordRetract_sum (y := ⟨_, (S _).1.1⟩) _ rfl, sub_smul, smul_sub, @sum_comm (Fin (finrank _ U)),
    ← smul_assoc, ← sum_smul, e.resolve_left n.1, S_smul]) (sum_smul_mem _ c (t :=
    univ) fun l _ ↦ have T := sub_mem (X l) (S (FrobGroup.φ ^ b • A l ·)); add_mem_sup
    (s := k.E • ∑ m, y l m • x (s m)) (t := coordRetract (⟨_, (X l).1.1⟩ - ⟨_, (S _).1.1⟩))
    (by simpa using! frobEUnit_zpow_mem_withExponents 0 1 (S _)) (coordRetract_mem_withExponents _
      (mem_withExponents_of_mem_hodgeFil T fun d v _ e μ m ↦ ?_)))⟩
  obtain ⟨rfl, rfl⟩ := by simpa [raiseExponent] using e.ne
  refine (sub_mem_iff_left _ (sum_mem fun m _ ↦ smul_of_tower_mem _ _ ?_)).1 (by simpa [valueAt]
    using! (valueAt_mem_of_hodgeFil_le _ T (R μ m).choose_spec))
  simpa [ht, raiseExponent, algebraMap.smul, sub_mul, sum_mul, add_comm, smul_distrib_smul,
    smul_sub, smul_sum, -Units.val_zpow_eq_zpow_val] using! mul_mem_hodgeFil (n :=
    o d v) (algebraMap_mem_hodgeFil_one_iff (y := t l m - ∑ i,
    A l i • t (s i) m).2 (by simpa [smul_def', ← z.coord_apply,
    mul_comm, *] using! congr($(z.sum_repr ⟨_, Pi.single m 1, rfl⟩).1 l).symm)) (subset_span rfl)

end Lift.KummerChart.JumpLattice

namespace Lift.KummerChart

attribute [-instance] LieRinehartAlgebra.toIsScalarTower

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {L : JumpLattice O} {x :
  L.Ambient} {l A : ℕ} {i : Letter} {o : ℤ → ℤ} {S : PairingSide O} (hl : 0 < l) (l : ℕ)

/-- The system of exponents obtained from the standard one of level l (0 for a < l, −u for a ≥
l) by adding o(u) at the point a = 0. -/
abbrev JumpLattice.shiftedStd (o : ℤ → ℤ) a u := stdExponent l a u + ite (0 = a) (o u) 0

/-- The Z_p-module of x in `Lift.KummerChart.JumpLattice.locLetterPart` l i such that every gx − x,
g in Γ', has at i the standard exponents of level l raised by A at E. -/
noncomputable def JumpLattice.constantsModE (A : ℕ) i := (L.locLetterPart l
  i).restrictScalars ℤ_[p] ⊓ invariantsMod (withExponents i (shiftedStd l fun _ ↦ A))

open algebraMap

/-- Let l > 0, s = w(s) + E·t(s) on S, w(s) ∈ Λ. Let v_a, c lie in Cs, the x in 𝒩 at i with
exponents `Lift.KummerChart.stdExponent` l and all gx − x of exponents sd l A
(`Lift.KummerChart.JumpLattice.shiftedStd`). If ∑ s_a v_a − f(E)c has exponents sd l o, o ≤ A, then
∑ w(tⁿs_a)v_a − f_n c lies in Cs, with exponents sd l o', o'(u) = A if o(u) > n, else 0. -/
lemma JumpLattice.coeff_mem_constantsModE {l A : ℕ} {i : Letter} {o : ℤ → ℤ} (hl : 0 < l) {w : _ →
  WittFq k.f} {t} (e : ∀ s, s - w s = k.E * t s) {m} {v : Fin m → _} (hv : ∀ a,
  v a ∈ L.constantsModE l A i) {c} (hc : c ∈ L.constantsModE l A i) n (s : _ → _) (f : ℤ[X]) (ho :
  ∀ u, o u ≤ A) (H : ∑ a, s a • v a - aeval k.E f • c ∈ withExponents i (shiftedStd l o)) :
  let d := ∑ a, (w (t^[n] (s a)) : k.S) • v a - f.coeff n • c
  d ∈ L.constantsModE l A i ∧ d ∈ withExponents i (shiftedStd l (if o · ≤ n then 0 else A)) := by
  induction' n using Nat.caseStrongRecOn with n ih generalizing s f o <;> have K := by simpa [
    add_smul, mul_smul, ← smul_sum, add_sub_add_comm, ← smul_sub, Int.cast_smul_eq_zsmul] using
    (funext (eq_add_of_sub_eq <| e <| s ·) ▸ f.X_mul_divX_add ▸ H :)
  refine ⟨?a, mem_withExponents_of_le (mem_withExponents_of_deep (lo := shiftedStd l (1 ⊓ o ·))
    ((add_mem_cancel_left (by simpa using! (frobEUnit_zpow_mem_withExponents 0 1
    (sub_mem (sum_smul_mem _ _ fun a _ ↦ (hv a).1.2) (smul_mem _ _ hc.1.2))))).1
    (mem_withExponents_of_le K)) ?a.2)⟩
  exact sub_mem (sum_mem fun a _ ↦
    ⟨smul_mem (locLetterPart ..) _ (hv a).1, fun ⟨_, γ, rfl⟩ ↦ by simpa [fixes,
    S_smul, frobGroup_smul_smul, smul_sub] using (smul_mem _ _ ((hv a).2 ⟨_, γ, rfl⟩))⟩) (by bound)
  simpa using ih _ .refl _ f.divX ((sub_one_lt _).le.trans <| ho ·) (Eq.subst (by
    simp [inv_smul_eq_iff]; rfl) (frobEUnit_zpow_mem_withExponents 0 (-1)
    (sub_mem K (mem_withExponents_of_le (ih 0 bot_le _ _ ho H).2))))

/-- For l > 0, let x in φ^l M have form values in the field 𝒦₀ that are Γ'-invariant modulo t^A.
Then its projection to i lies in φ^{l*}N, with depth A at E and the standard exponents of
level l elsewhere. -/
lemma JumpLattice.letterProj_mem_constantsModE {l : ℕ} (hl : 0 < l) i
    (H : x ∈ L.valueFieldPoints (frobKisinAinf l) ∧ ∀ μ ∈ L.forms, ∀ g : k.Γ', toGp g • μ x - μ x ∈
  hodgeFil A) : L.letterProj i x ∈ L.constantsModE l A i := (fun y ↦ ⟨y, fun ⟨_, γ, rfl⟩ ↦
  mem_withExponents_of_mem_hodgeFil (smul_sub_mem_withExponents y.2 _) (·.rec (fun _ _ _ _ m ↦ by
  simpa [shiftedStd, stdExponent, hl, ↓valueAt_smul_sub y.1.1 m.1] using!
    H.2 _ (comp_letterProj_mem_forms m.1) γ) (by simp))⟩) (letterProj_mem_of_valueFieldPoints H.1)

/-- Long gap, unramified chart, l > 0: if p^κ kills l letters before i, E^s kills at i, the
jumps between are ≤ g, N = s + gΣ_{t<l} p^t < A ≤ p^l δ, 3 ≤ p^l, then a point over
p^{κ+4δ}c has exponents min(A, −u−N), depth A at E, both standard elsewhere. -/
lemma PairingSide.pointsOver_nonempty_of_long_gap {l : ℕ} (hl : 0 < l) (hk :
  IsUnramified) {κ s g δ N : ℕ} (hK : S.KillsCokernel (i.stepBack l) κ 0) (hz : S.KillsCokernel i
  0 s) (hN : s + g * ∑ t ∈ Finset.range l, p ^ t = N) (hg : ∀ t < l, ∀ u ∈ S.U (i.stepBack t), u ≤
  g) (hA : N < A) (hq : 3 * k.e ≤ p ^ l) (hδ : k.e * A ≤ p ^ l * δ) c : (S.pointsOver c i
  (κ + 4 * δ) (shiftedStd l fun u ↦ min A (-u - N)) (shiftedStd l fun _ ↦ A)).Nonempty := by
  have ⟨y, hy, F, H, _⟩ := pointsOver_nonempty_of_killsCokernel hz c
  have ⟨f, hf, H⟩ : ∃ f : ℤ[X], f.IsMonicOfDegree N ∧ aeval k.E f • y ∈ withExponents i fun a ↦
    (ite (a < l) g 0 - ·) := hN ▸ l.rec ⟨_, isMonicOfDegree_X_pow .., by
    simpa [frobEUnit_pow_smul] using! frobEUnit_zpow_mem_withExponents 0 s H⟩ fun l ⟨f, hf, H⟩ ↦ ⟨_,
    Eq.subst (by grind [sum_range_succ]) (((((isMonicOfDegree_X_sub_one ↑p).pow (p ^ l)).add_right
    (q := p) (by simp [NeZero.pos])).pow g).mul hf), by simpa [frobEUnit_pow_smul, frobE_eq,
    phi_pow_smul_z, hk.1, mul_smul] using! frobEUnit_zpow_mem_withExponents l g H⟩
  have ⟨_, r, v, E⟩ := mem_span_set'.1 (frame_theorem.1.2.1 l A δ hq hδ _
    ⟨(mem_withExponents_stdExponent_iff.1 (mem_withExponents_of_le H)).1, (smul_mem _ _ hy).2⟩)
  apply_fun letterProj i at E; simp [mem_letterPart_iff_letterProj.1 H.1.2] at E
  choose w t et using
    (by simpa [Algebra.smul_def] using k.exists_dvd_sub_sum_z_pow 0 (by simp [hk.2] : _ = 1) ·)
  obtain ⟨⟨⟨b, d⟩, d₁⟩, a, d₂⟩ := coeff_mem_constantsModE hl et
    (letterProj_mem_constantsModE hl i <| v · |>.2) (ZeroMemClass.zero_mem _) N r 0
    (min_le_left _ <| g - ·) (by simpa [E] using nsmul_mem (mem_withExponents_of_le H) _),
    coeff_mem_constantsModE hl et (letterProj_mem_constantsModE hl i <| v · |>.2.imp (.imp
    S.projTriv.wittMap_mem_frobKisinAinf fun H _ ↦ H _ ∘ S.projTriv.comp_wittMap_mem_forms) fun H
    _ ↦ H _ ∘ S.projTriv.comp_wittMap_mem_forms) ⟨constantAt_mem_locLetterPart c,
    (by simp [k.galMonoid.smul_def, constantAt, gal_smul_letterProj ·])⟩ N r (p ^ (4 * δ) •
    f) (fun _ ↦ le_rfl) (by simp [by simpa using congr(S.projTriv.wittMap $E), F, -nsmul_eq_mul])
  obtain ⟨v, ⟨hv, n⟩, q⟩ := (exists_lift_of_mem_liftIdeal (f :=
    p ^ κ) (by simpa using (phi_pow_mem_liftIdeal_iff l).2 hK)).choose_spec _
    ⟨frobEUnit_zpow_smul_mem_kisinLoc.2 a.1.1,
    frobEUnit_zpow_mem_withExponents 0 (-A) d₂ (by clear * - hA; grind)⟩
  exact ⟨_, sub_mem (nsmul_mem b.1 (p ^ κ)) (frobEUnit_zpow_smul_mem_kisinLoc.2 hv), by
    simp [q, smul_comm (_ ^ A), ← hf.1, hf.2, -nsmul_eq_mul]; module, sub_mem (nsmul_mem
    (mem_withExponents_of_le d₁ (by clear * - hA; grind)) _)
    (frobEUnit_zpow_mem_withExponents 0 _ n),
    sub_mem (nsmul_mem d _) (smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents 0 A n))⟩
