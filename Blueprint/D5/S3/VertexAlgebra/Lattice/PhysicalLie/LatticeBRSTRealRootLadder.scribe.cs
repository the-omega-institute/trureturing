using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.PhysicalLie;

internal sealed class LatticeBRSTRealRootLadderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        @"Original physical real-root adjoint injectivity and surjectivity",
        H(@"Original physical real-root adjoint injectivity and surjectivity"), Blocks(
            Paragraph(Text(@"The full original module-level telescope is D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) ℂ, h26 : D.rank = 26, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1. D retains its original integral symmetric Gram matrix and even diagonal. H is complex and satisfies BOTH displayed inverse equations. Put C = Cohomology D H h26 hHG hGH, Ph = physicalImage D H h26 hHG hGH and Fib = physicalChargeFiber D H h26 hHG hGH. Fix alpha : Charge D, hα : chargeEnergy D alpha = 1, e : Ph, he : (e : C) ∈ Fib alpha and he0 : e ≠ 0. These module and Root-section variables are part of both original declarations, beyond their theorem-local beta, pairing, c and hc arguments.")),
            Paragraph(Text(@"C is the original global cohomology: cycles are ker Q for Q = totalCharge D H, and boundaries are the global image of Q from all original State D. Ph is literally the range of the original physicalClass map inside C; it retains the original physical representative equations Qx = 0, B_0 x = 0, Nx = x and totalL0 D H x = 0. Its bracket is the already descended original current, restricted to that image. Fib is literally the original physicalChargeFiber inside the same C, retaining the actual charge condition; it is not a replacement quotient. In BOTH quotient slots the boundary primitives remain arbitrary original State D, with no physical, relative, homogeneous, zero-energy or fixed-charge restriction. All original lattice charges and epsilon conventions are retained.")),
            Paragraph(Text(@"Write fα = normalizedOpposite D H h26 hHG hGH alpha hα e he he0 and hαC = cartanPhysicalImage D H h26 hHG hGH (fun i => (alpha i : ℂ)). On the actual Ph set E = LieModule.toEnd ℂ Ph Ph e and F = LieModule.toEnd ℂ Ph Ph fα. The physical_sl2 helper uses the supplied sl2_ef, sl2_he and sl2_hf relations; hαC ≠ 0 follows from [hαC,e] = 2 • e and he0. The supplied cartan_adjoint and gamma_charge give [hαC,c] = (bilinear D alpha beta : ℂ) • c for c in Fib beta. Supplied positive_root_adjoint_locally_nilpotent is applied pointwise on this literal Ph: at -alpha and fα in the negative proof, and at alpha and e in the positive proof. normalizedOpposite_mem, opposite_positive, root_positive and iterate_mem_fiber retain their original supplier meanings.")),
            Paragraph(Text(@"Both pairing statements quantify EVERY beta : Charge D and EVERY c : Ph subject to hc and the displayed CONDITIONAL integral pairing inequality. No nonzero-beta or nonzero-c hypothesis is added. Zero charge remains in the quantified domain; the inequality determines applicability. For beta = alpha the positive statement permits a preimage in Fib (alpha - alpha), the original zero-charge fiber. c = 0 is included, and the positive proof explicitly treats killing bound N = 0 by c = 0 and d = 0. The hypotheses add no lattice positivity, realness of H, signature, unimodularity, perfectness, Noetherianity, global finite dimension, HPL invariance or convergence premise; no uniform nilpotence exponent is required.")),
            Paragraph(Text(@"There are exactly seven new private helpers in the delivered Lean source, all consumed and none registered here: (1) lowering_weight proves the h-weight w - 2n of F^n v from the h-weight w of v, without assuming E v = 0; (2) raising_lowering_commutator consumes it to prove E(F^(n+1)v) = F^(n+1)(Ev) + (n+1)(w-n) • F^n v for a general weight vector; (3) diagonal_commutator consumes that identity and Mathlib's raising-weight formula at E^n c to obtain coefficient (n+1)(mu+n); (4) ladderCoefficient is the actual recursive coefficient definition a_0 = (mu : ℂ)⁻¹ and a_(n+1) = -a_n / ((n+2)(mu+n+1)); (5) ladderCoefficient_step proves a_(n+1)((n+2)(mu+n+1)) = -a_n using positive integral mu; (6) finite_ladder_telescope consumes the diagonal identity, coefficient definition and coefficient step to prove the finite sum identity used by surjectivity; (7) physical_sl2 constructs the actual triple used by BOTH public theorems. The coefficient definition is also consumed in the public preimage. This is six private theorems and one private definition, with actual transitive proof consumption, not seven public registrations.")),
            Describe.Lean(DescribeId.Create(@"latticebrstrealrootladder-injective-negative-pairing"),
                DeclarationHandle.Create(@"D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootLadder.real_root_adjoint_injective_of_negative_pairing"),
                H(@"Negative pairing gives zero kernel for the actual root adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(@"The full original module-level telescope is D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) ℂ, h26 : D.rank = 26, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1. D retains its original integral symmetric Gram matrix and even diagonal. H is complex and satisfies BOTH displayed inverse equations. Put C = Cohomology D H h26 hHG hGH, Ph = physicalImage D H h26 hHG hGH and Fib = physicalChargeFiber D H h26 hHG hGH. Fix alpha : Charge D, hα : chargeEnergy D alpha = 1, e : Ph, he : (e : C) ∈ Fib alpha and he0 : e ≠ 0. These module and Root-section variables are part of both original declarations, beyond their theorem-local beta, pairing, c and hc arguments.

Exact complete public Lean header, including the proof introducer:
theorem real_root_adjoint_injective_of_negative_pairing
    (beta : Charge D) (hlambda : bilinear D alpha beta < 0)
    (c : Ph) (hc : (c : C) ∈ Fib beta) (hec : ⁅e, c⁆ = 0) : c = 0 := by

Let lambda = bilinear D alpha beta < 0 and assume E c = 0. The proof argues by contradiction from c ≠ 0 and forms the actual primitive vector for physical_sl2. F-local nilpotence on c and Nat.exists_not_and_succ_of_not_zero_of_exists yield n with F^n c ≠ 0 and F^(n+1)c = 0. Mathlib's HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f gives 0 = ((n : ℂ)+1)((lambda : ℂ)-(n : ℂ)) • F^n c. Since lambda is a negative integer and n is natural, both scalar factors are nonzero, contradicting F^n c ≠ 0. The conclusion is the exact kernel-zero statement c = 0 on the original fiber; it is injectivity of the actual left adjoint restricted to that fiber. This is the primitive formula proof implemented in the sealed source."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create(@"latticebrstrealrootladder-surjective-positive-pairing"),
                DeclarationHandle.Create(@"D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootLadder.real_root_adjoint_surjective_of_positive_pairing"),
                H(@"Positive pairing gives a preimage in the original beta-alpha fiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(@"The full original module-level telescope is D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) ℂ, h26 : D.rank = 26, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1. D retains its original integral symmetric Gram matrix and even diagonal. H is complex and satisfies BOTH displayed inverse equations. Put C = Cohomology D H h26 hHG hGH, Ph = physicalImage D H h26 hHG hGH and Fib = physicalChargeFiber D H h26 hHG hGH. Fix alpha : Charge D, hα : chargeEnergy D alpha = 1, e : Ph, he : (e : C) ∈ Fib alpha and he0 : e ≠ 0. These module and Root-section variables are part of both original declarations, beyond their theorem-local beta, pairing, c and hc arguments.

Exact complete public Lean header, including the proof introducer:
theorem real_root_adjoint_surjective_of_positive_pairing
    (beta : Charge D) (hmu : 0 < bilinear D alpha beta)
    (c : Ph) (hc : (c : C) ∈ Fib beta) :
    ∃ d : Ph, (d : C) ∈ Fib (beta - alpha) ∧ ⁅e, d⁆ = c := by

Let mu = bilinear D alpha beta > 0. The proof obtains a pointwise killing bound K with E^K c = 0. If K = 0, then c = 0 and it returns d = 0 in Fib (beta-alpha). If K = N+1, it takes exactly d = ∑ n ∈ Finset.range (N+1), a_n • F^(n+1)(E^n c), with the actual ladderCoefficient above. E^n c need not be primitive. The general commutator and its diagonal specialization give E(F^(n+1)E^n c) = F^(n+1)E^(n+1)c + (n+1)(mu+n) • F^n E^n c. Positivity of integral mu makes the coefficient denominators nonzero. The delivered finite_ladder_telescope proves E d = c + a_N • F^(N+1)(E^(N+1)c); the final term vanishes by the chosen bound. iterate_mem_fiber first at alpha and then at -alpha gives every summand the literal original charge beta + n • alpha + (n+1) • (-alpha) = beta-alpha. Submodule sum and scalar closure put d in the actual Fib (beta-alpha). Only this finite coefficient telescope is used, with no duality or finite-dimensional whole-image argument."))), DescribeRole.Theorem),
            Paragraph(Text(@"The mathematics is classical sl2 representation theory. Mathlib.Algebra.Lie.Sl2 supplies the primitive-vector and raising-weight formulas (Oliver Nash and Mathlib contributors). The delivered source proves and consumes its general nonprimitive commutator and finite telescope on the actual physical carrier. Original lattice/VOA/BRST suppliers retain Bakalov--Kac, Scott Carnahan, Kalle Kytölä, Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman attribution. Batteries supplies exact private-declaration access. No accepted Pro answer is relied upon. These two ladder statements do not claim Monster/Borcherds recognition, a denominator identity, or complete Monster/VOA/CFT/anomaly/fusion/string/AdS mathematics.")),
            Paragraph(Text(@"SOURCE_ONLY_UNCOMPILED. This is canonical Scribe SOURCE integration only. Source-specific typed Reg audit, native C# compilation, Scribe rendering and enrollment, native Lean elaboration/kernel/axiom validation of the unchanged candidate and its pending suppliers, required repository checks, PR and publication remain pending. The document structure follows the two sealed tracked template snapshots; this source check supplies no native acceptance receipt. The full goal remains ACTIVE INCOMPLETE.")),
            Paragraph(Text(@"Complete unchanged sealed Lean source follows; this literal is an unchanged supplier, not a new proof or native validation:
/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootLadder
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTRealRootLadder
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Original physical real-root adjoint injectivity and surjectivity. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection
import Mathlib.Algebra.Lie.Sl2
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-!
SOURCE_ONLY_UNCOMPILED. These are proof-source candidates, with no native
elaboration, kernel, axiom-closure, C#, Reg or publication acceptance claimed.
The sealed integrability, Cartan-character, generic exponential and Weyl
sources remain pending native checking. The accepted196 OppositeRootBracket
is the supplier; no older surgical version is substituted.

C is the original global Cohomology, Ph is literally physicalImage and Fib
is literally physicalChargeFiber. Boundary primitives in BOTH quotient slots
remain arbitrary original State D. H is COMPLEX with BOTH inverse equations.
Every beta is quantified; the pairing inequalities are conditional. Neither
beta=0 nor beta=alpha nor c=0 is excluded. No whole-space finite-dimensional,
Noetherian, norm, signature, positivity, realness or convergence hypothesis is
added. N=0 is handled explicitly in the surjectivity proof.

The mathematics is classical sl2 representation theory. The primitive-vector
formula and raising-weight formula are reused from Mathlib (Oliver Nash and
Mathlib contributors). The nonprimitive lowering commutator and finite
right-inverse telescope are proved below and consumed on the actual physical
carrier. Original physical suppliers retain Bakalov--Kac, Scott Carnahan,
Kalle Kytölä, Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman
attribution. Batteries supplies exact private-declaration access. This is no
Monster/Borcherds recognition, denominator identity or full string theorem.
The full Monster/VOA/CFT/anomaly/fusion/string/AdS goal is ACTIVE INCOMPLETE.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

-- These are MODULE paths. Their ordinary namespaces are opened separately.
open private normalizedOpposite_mem root_positive opposite_positive
  gamma_charge sl2_ef sl2_he sl2_hf from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootWeylReflection
open private iterate_mem_fiber from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootLadder

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy)
open LatticeBRSTCohomologyField (Cohomology)
open LatticeBRSTPhysicalLie (physicalImage)
open LatticeBRSTPhysicalChargeFiber (physicalChargeFiber)
open LatticeBRSTNeutralPhysicalCartan (cartanPhysicalImage cartan_adjoint)
open LatticeBRSTRealRootWeylReflection (normalizedOpposite)
open LatticeBRSTPositiveRootIntegrability (positive_root_adjoint_locally_nilpotent)
open LieModule (toEnd toEnd_apply_apply)

section Algebra

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {h e f : L} (t : IsSl2Triple h e f)

local notation ""E"" => toEnd ℂ L L e
local notation ""F"" => toEnd ℂ L L f

-- The h-weight formula for F^n v does not require E v = 0.
include t in
private theorem lowering_weight (v : L) (w : ℂ)
    (hv : ⁅h, v⁆ = w • v) (n : ℕ) :
    ⁅h, (F ^ n) v⁆ = (w - 2 * (n : ℂ)) • (F ^ n) v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply,
        Nat.cast_add, Nat.cast_one, leibniz_lie h,
        t.lie_lie_smul_f ℂ, ← neg_smul, ih, lie_smul, smul_lie,
        ← add_smul]
      congr 1
      ring

-- GENERAL nonprimitive commutator: no assertion that E v vanishes.
include t in
private theorem raising_lowering_commutator (v : L) (w : ℂ)
    (hv : ⁅h, v⁆ = w • v) (n : ℕ) :
    ⁅e, (F ^ (n + 1)) v⁆ =
      (F ^ (n + 1)) ⁅e, v⁆ +
        (((n : ℂ) + 1) * (w - (n : ℂ))) • (F ^ n) v := by
  have hF (k : ℕ) (z : L) : ⁅f, (F ^ k) z⁆ = (F ^ (k + 1)) z := by
    rw [pow_succ', Module.End.mul_apply]
    rfl
  induction n with
  | zero =>
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply,
        toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        leibniz_lie e, t.lie_e_f, hv]
      abel
  | succ n ih =>
      calc
        ⁅e, (F ^ (n + 1 + 1)) v⁆ =
            ⁅h, (F ^ (n + 1)) v⁆ + ⁅f, ⁅e, (F ^ (n + 1)) v⁆⁆ := by
          rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply,
            leibniz_lie e, t.lie_e_f]
        _ = (w - 2 * ((n + 1 : ℕ) : ℂ)) • (F ^ (n + 1)) v +
            ⁅f, (F ^ (n + 1)) ⁅e, v⁆ +
              (((n : ℂ) + 1) * (w - (n : ℂ))) • (F ^ n) v⁆ := by
          rw [lowering_weight t v w hv (n + 1), ih]
        _ = (F ^ (n + 1 + 1)) ⁅e, v⁆ +
            ((((n + 1 : ℕ) : ℂ) + 1) * (w - ((n + 1 : ℕ) : ℂ))) •
              (F ^ (n + 1)) v := by
          rw [lie_add, lie_smul, hF (n + 1) ⁅e, v⁆, hF n v]
          push_cast
          module

-- E^n c is usually NOT primitive. This is the diagonal identity actually
-- used by the telescope, obtained from the general commutator above.
include t in
private theorem diagonal_commutator (c : L) (mu : ℤ)
    (hc : ⁅h, c⁆ = (mu : ℂ) • c) (n : ℕ) :
    ⁅e, (F ^ (n + 1)) ((E ^ n) c)⁆ =
      (F ^ (n + 1)) ((E ^ (n + 1)) c) +
        (((n : ℂ) + 1) * ((mu : ℂ) + (n : ℂ))) • (F ^ n) ((E ^ n) c) := by
  have hw := t.lie_h_pow_toEnd_e hc n
  have hg := raising_lowering_commutator t ((E ^ n) c)
    ((mu : ℂ) + 2 * (n : ℂ)) hw n
  rw [IsSl2Triple.lie_e_pow_toEnd_e n] at hg
  have hs : (mu : ℂ) + 2 * (n : ℂ) - (n : ℂ) =
      (mu : ℂ) + (n : ℂ) := by ring
  simpa only [hs] using hg

private def ladderCoefficient (mu : ℤ) : ℕ → ℂ
  | 0 => (mu : ℂ)⁻¹
  | n + 1 => -ladderCoefficient mu n /
      (((n : ℂ) + 2) * ((mu : ℂ) + (n : ℂ) + 1))

private theorem ladderCoefficient_step (mu : ℤ) (hmu : 0 < mu) (n : ℕ) :
    ladderCoefficient mu (n + 1) *
        (((n : ℂ) + 2) * ((mu : ℂ) + (n : ℂ) + 1)) =
      -ladderCoefficient mu n := by
  have hn : (n : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show (n : ℤ) + 2 ≠ 0 by omega)
  have hm : (mu : ℂ) + (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show mu + (n : ℤ) + 1 ≠ 0 by omega)
  exact div_mul_cancel₀ _ (mul_ne_zero hn hm)

-- A vectorwise finite identity; N+1 is the number of terms. No uniform
-- exponent, invariant finite-dimensional span or analytic exponential occurs.
include t in
private theorem finite_ladder_telescope (c : L) (mu : ℤ) (hmu : 0 < mu)
    (hc : ⁅h, c⁆ = (mu : ℂ) • c) (N : ℕ) :
    ⁅e, ∑ n ∈ Finset.range (N + 1),
      ladderCoefficient mu n • (F ^ (n + 1)) ((E ^ n) c)⁆ =
      c + ladderCoefficient mu N • (F ^ (N + 1)) ((E ^ (N + 1)) c) := by
  induction N with
  | zero =>
      have hm : (mu : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hmu)
      have hd : ⁅e, (F ^ 1) c⁆ = (F ^ 1) ((E ^ 1) c) + (mu : ℂ) • c := by
        simpa only [Nat.cast_zero, zero_add, add_zero, one_mul,
          pow_zero, Module.End.one_apply] using diagonal_commutator t c mu hc 0
      simp only [Finset.sum_range_one, pow_zero, Module.End.one_apply]
      rw [lie_smul, hd, smul_add, smul_smul]
      have ha : ladderCoefficient mu 0 * (mu : ℂ) = 1 := inv_mul_cancel₀ hm
      rw [ha, one_smul]
      abel
  | succ N ih =>
      rw [Finset.sum_range_succ, lie_add, ih, lie_smul,
        diagonal_commutator t c mu hc (N + 1), smul_add, smul_smul]
      have hden : ((((N + 1 : ℕ) : ℂ) + 1) *
          ((mu : ℂ) + ((N + 1 : ℕ) : ℂ))) =
          (((N : ℂ) + 2) * ((mu : ℂ) + (N : ℂ) + 1)) := by
        push_cast
        ring
      rw [hden, ladderCoefficient_step mu hmu N]
      module

end Algebra

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation ""C"" => Cohomology D H h26 hHG hGH
local notation ""Ph"" => physicalImage D H h26 hHG hGH
local notation ""Fib"" => physicalChargeFiber D H h26 hHG hGH

section Root

variable (alpha : Charge D) (hα : chargeEnergy D alpha = 1)
  (e : Ph) (he : (e : C) ∈ Fib alpha) (he0 : e ≠ 0)

local notation ""fα"" => normalizedOpposite D H h26 hHG hGH alpha hα e he he0
local notation ""hαC"" => cartanPhysicalImage D H h26 hHG hGH (fun i => (alpha i : ℂ))

include hα he he0

private theorem physical_sl2 : IsSl2Triple hαC e fα := by
  have hh : hαC ≠ 0 := by
    intro hh
    have hz : (2 : ℂ) • e = 0 := by
      simpa only [hh, zero_lie] using
        (sl2_he D H h26 hHG hGH alpha hα e he he0).symm
    exact he0 ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  exact
    { h_ne_zero := hh
      lie_e_f := sl2_ef D H h26 hHG hGH alpha hα e he he0
      lie_h_e_nsmul := by
        simpa only [two_smul] using sl2_he D H h26 hHG hGH alpha hα e he he0
      lie_h_f_nsmul := by
        simpa only [neg_smul, two_smul] using
          sl2_hf D H h26 hHG hGH alpha hα e he he0 }

/-- On every original charge fiber of negative alpha-pairing, the actual
left root adjoint has zero kernel. No nonzero-charge or nonzero-c premise. -/
theorem real_root_adjoint_injective_of_negative_pairing
    (beta : Charge D) (hlambda : bilinear D alpha beta < 0)
    (c : Ph) (hc : (c : C) ∈ Fib beta) (hec : ⁅e, c⁆ = 0) : c = 0 := by
  classical
  by_contra hc0
  let t := physical_sl2 D H h26 hHG hGH alpha hα e he he0
  have hw : ⁅hαC, c⁆ = (bilinear D alpha beta : ℂ) • c := by
    rw [cartan_adjoint D H h26 hHG hGH _ beta c hc.2, gamma_charge]
  have P : t.HasPrimitiveVectorWith c (bilinear D alpha beta : ℂ) :=
    { ne_zero := hc0, lie_h := hw, lie_e := hec }
  obtain ⟨N, hN⟩ := positive_root_adjoint_locally_nilpotent D H h26 hHG hGH
    (-alpha) (opposite_positive D alpha hα) fα
    (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0) c
  have hFN : ((toEnd ℂ Ph Ph fα) ^ N) c = 0 := by
    rw [Module.End.pow_apply]
    exact hN
  obtain ⟨n, hn, hns⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun k => ((toEnd ℂ Ph Ph fα) ^ k) c = 0)
    (by simpa using hc0) ⟨N, hFN⟩
  have hscalar : (bilinear D alpha beta : ℂ) - (n : ℂ) ≠ 0 := by
    exact_mod_cast (show bilinear D alpha beta - (n : ℤ) ≠ 0 by omega)
  have hcoef : ((n : ℂ) + 1) *
      ((bilinear D alpha beta : ℂ) - (n : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_add_one_ne_zero n) hscalar
  have hformula := P.lie_e_pow_succ_toEnd_f n
  rw [hns, lie_zero] at hformula
  exact (smul_ne_zero hcoef hn) hformula.symm

/-- On every original charge fiber of positive alpha-pairing, the actual
left root adjoint is onto from the literal beta-alpha fiber. In particular
beta=alpha is allowed and its preimage has zero original charge. -/
theorem real_root_adjoint_surjective_of_positive_pairing
    (beta : Charge D) (hmu : 0 < bilinear D alpha beta)
    (c : Ph) (hc : (c : C) ∈ Fib beta) :
    ∃ d : Ph, (d : C) ∈ Fib (beta - alpha) ∧ ⁅e, d⁆ = c := by
  classical
  let t := physical_sl2 D H h26 hHG hGH alpha hα e he he0
  let E : Module.End ℂ Ph := toEnd ℂ Ph Ph e
  let F : Module.End ℂ Ph := toEnd ℂ Ph Ph fα
  have hw : ⁅hαC, c⁆ = (bilinear D alpha beta : ℂ) • c := by
    rw [cartan_adjoint D H h26 hHG hGH _ beta c hc.2, gamma_charge]
  obtain ⟨N, hN⟩ := positive_root_adjoint_locally_nilpotent D H h26 hHG hGH
    alpha (root_positive D alpha hα) e he c
  have hEN : (E ^ N) c = 0 := by
    rw [Module.End.pow_apply]
    exact hN
  cases N with
  | zero =>
      have hc0 : c = 0 := by simpa using hEN
      refine ⟨0, (Fib (beta - alpha)).zero_mem, ?_⟩
      simp only [lie_zero, hc0]
  | succ N =>
      have hterm (n : ℕ) : ((F ^ (n + 1)) ((E ^ n) c) : C) ∈
          Fib (beta - alpha) := by
        have hE : ((E ^ n) c : C) ∈ Fib (beta + (n : ℤ) • alpha) := by
          rw [Module.End.pow_apply]
          exact iterate_mem_fiber D H h26 hHG hGH alpha beta e he n c hc
        have hF := iterate_mem_fiber D H h26 hHG hGH (-alpha)
          (beta + (n : ℤ) • alpha) fα
          (normalizedOpposite_mem D H h26 hHG hGH alpha hα e he he0)
          (n + 1) ((E ^ n) c) hE
        have hcharge : beta + (n : ℤ) • alpha +
            ((n + 1 : ℕ) : ℤ) • (-alpha) = beta - alpha := by
          push_cast
          module
        rw [hcharge] at hF
        rw [Module.End.pow_apply]
        exact hF
      let d : Ph := ∑ n ∈ Finset.range (N + 1),
        ladderCoefficient (bilinear D alpha beta) n •
          (F ^ (n + 1)) ((E ^ n) c)
      refine ⟨d, ?_, ?_⟩
      · change (physicalImage D H h26 hHG hGH).subtype
          (∑ n ∈ Finset.range (N + 1),
            ladderCoefficient (bilinear D alpha beta) n •
              (F ^ (n + 1)) ((E ^ n) c)) ∈ Fib (beta - alpha)
        rw [map_sum]
        apply (Fib (beta - alpha)).sum_mem
        intro n _
        change ladderCoefficient (bilinear D alpha beta) n •
          ((F ^ (n + 1)) ((E ^ n) c) : C) ∈ Fib (beta - alpha)
        exact (Fib (beta - alpha)).smul_mem _ (hterm n)
      · change ⁅e, ∑ n ∈ Finset.range (N + 1),
          ladderCoefficient (bilinear D alpha beta) n •
            (F ^ (n + 1)) ((E ^ n) c)⁆ = c
        rw [finite_ladder_telescope t c (bilinear D alpha beta) hmu hw N]
        rw [hEN, map_zero, smul_zero, add_zero]

end Root
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRealRootLadder
")))));
}
