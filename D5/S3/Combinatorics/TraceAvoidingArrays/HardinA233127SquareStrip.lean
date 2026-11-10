/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127SquareStrip.finite_certificate
   digest: Hardin's recurrence for literal normalized six-column square strips. -/

/-
admission_basis: open-problem-resolution (#28649; Proved)
escape_witness: none; every declaration is bind-only. The all-height reduction v_eq_w
instantiates Function.Semiconj.iterate_right after normalization of finite one-step premises.
Direct frozen dependencies (declaration statement_ids from scoped-lean-report.json):
Indented name fragments concatenate without whitespace.
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.advance
statement_id: sha256:63e23e390cbc7ee42155ce307351f149d901cd9013daee3d6d2eac775e24af71
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.allowed
statement_id: sha256:4ee019eb42606605da41b2b090212be244d3bf48d64a2c10dc2d9c6c6f7e6468
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_fst
statement_id: sha256:5859cc0f84f4e6a91313521f32ea6d187c4822bb52d4e438939da5e000940bd5
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_snd
statement_id: sha256:1ada14ea452d6f35f959dbbd5a034265c8c6921cd041422cad27ec166a94d24c
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good_iff
statement_id: sha256:59d0ffb034f7f2361718e6d2566eb24417785b9a178f6fcb44f336c1199d3d62
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.instDecidableAllowed
statement_id: sha256:9e135f0d9ab09759e51e42b0ac88f4af874ef89f0e507400af6cd5a57f0dee70
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableLegal
statement_id: sha256:6c1f0ba304e14673a1966eca92d67e12ccf8925c940c5ba2391b4b478ac39547
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthLegal
statement_id: sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthNormal._proof_1
statement_id: sha256:3ea64915f32c9d14cb1f8694caa8b29adcc02a50f28a6142292cccc5f150cf1a
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthStep
statement_id: sha256:bd12c5c5928f8822063ec100e0e6e92c5300f5907da4aa64e85595a1ee4c7cb5
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthStep.eq_1
statement_id: sha256:f0e1fc897c2470d95f639750def23fe05e87fb9061f66dd0ca788b6eda04aec4
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthTotal
statement_id: sha256:c4c082551693765b0f6c344f5f6ff825120f019a96ec4d79015c10c10bf774d0
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthTotal.eq_1
statement_id: sha256:98c91caccabbd60e8a6fae4d99818e8a614dfba06487712acc8167120f8e9727
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV
statement_id: sha256:4f3953ec5d8902b74486197a6f4d782f3fb58c6627a5740a5242632a7560f9ed
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV.eq_2
statement_id: sha256:02a910fcd311188b871be135dbe86f61c98a47ead76d48f62a22196f30991d60
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.width_counting_bridge
statement_id: sha256:a6ad861eda2ca48bc91989542e4b7cc27d81aec8df9a91b8db40c9398c577c72
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.Row
statement_id: sha256:802cb5ae5b1814d265a7f8260b6ae53ed440670a08e01fb25e907eae05cf25e2
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.instDecidableRowLegal
statement_id: sha256:1e2096782fbf116bcad750d1cf1a85ecfe80c177ff80c8bfc511f3fd3aa73502
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.rowLegal
statement_id: sha256:2d91f9276780b383fca63c8cbf77e7bd1468b9f2f59f66437cc1fb3f213c3bec
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.Boundary
statement_id: sha256:246a1b67905a4672aa678850d44d971890f326da2f56a1daefc1c2955945db79
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.full_row
statement_id: sha256:f81e65c6e42bf750ca73737a7ace4b7b696a7b7a57684908ba1ce134acfcf88c
D5.S3.Observer.Separation.BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
declaration:
  _private.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.0.D5.S3.
  Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.WidthRow
statement_id: sha256:63d18919d9321000a9a3541c82cd4a7aa88a0da2c26ce61e51d7cede756ff789
Local declaration names and consumers use the surrounding Lean namespace.
bonds: proof_shape=bind-only; consumers=a
decidableBonds: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge
labels: proof_shape=bind-only; consumers=class_fibres
compatible: proof_shape=bind-only; consumers=class_fibres
decidableCompatible: proof_shape=bind-only; consumers=classCount
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=valid_next
boundaryClass: proof_shape=bind-only; consumers=row_counts
transfer: proof_shape=bind-only; consumers=w
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=class_fibres
firstCount: proof_shape=bind-only; consumers=first_fibres
class_fibres: proof_shape=bind-only; consumers=class_fibres_normalized
class_fibres_normalized: proof_shape=bind-only; consumers=completed_010101
completed_010101: proof_shape=bind-only; consumers=row_counts
completed_010102: proof_shape=bind-only; consumers=row_counts
completed_010120: proof_shape=bind-only; consumers=row_counts
completed_010121: proof_shape=bind-only; consumers=row_counts
completed_010201: proof_shape=bind-only; consumers=row_counts
completed_010202: proof_shape=bind-only; consumers=row_counts
completed_010210: proof_shape=bind-only; consumers=row_counts
completed_010212: proof_shape=bind-only; consumers=row_counts
completed_012010: proof_shape=bind-only; consumers=row_counts
completed_012012: proof_shape=bind-only; consumers=row_counts
completed_012020: proof_shape=bind-only; consumers=row_counts
completed_012021: proof_shape=bind-only; consumers=row_counts
completed_012101: proof_shape=bind-only; consumers=row_counts
completed_012102: proof_shape=bind-only; consumers=row_counts
completed_012120: proof_shape=bind-only; consumers=row_counts
completed_012121: proof_shape=bind-only; consumers=row_counts
completed_020101: proof_shape=bind-only; consumers=row_counts
completed_020102: proof_shape=bind-only; consumers=row_counts
completed_020120: proof_shape=bind-only; consumers=row_counts
completed_020121: proof_shape=bind-only; consumers=row_counts
completed_020201: proof_shape=bind-only; consumers=row_counts
completed_020202: proof_shape=bind-only; consumers=row_counts
completed_020210: proof_shape=bind-only; consumers=row_counts
completed_020212: proof_shape=bind-only; consumers=row_counts
completed_021010: proof_shape=bind-only; consumers=row_counts
completed_021012: proof_shape=bind-only; consumers=row_counts
completed_021020: proof_shape=bind-only; consumers=row_counts
completed_021021: proof_shape=bind-only; consumers=row_counts
completed_021201: proof_shape=bind-only; consumers=row_counts
completed_021202: proof_shape=bind-only; consumers=row_counts
completed_021210: proof_shape=bind-only; consumers=row_counts
completed_021212: proof_shape=bind-only; consumers=row_counts
completed_101010: proof_shape=bind-only; consumers=row_counts
completed_101012: proof_shape=bind-only; consumers=row_counts
completed_101020: proof_shape=bind-only; consumers=row_counts
completed_101021: proof_shape=bind-only; consumers=row_counts
completed_101201: proof_shape=bind-only; consumers=row_counts
completed_101202: proof_shape=bind-only; consumers=row_counts
completed_101210: proof_shape=bind-only; consumers=row_counts
completed_101212: proof_shape=bind-only; consumers=row_counts
completed_102010: proof_shape=bind-only; consumers=row_counts
completed_102012: proof_shape=bind-only; consumers=row_counts
completed_102020: proof_shape=bind-only; consumers=row_counts
completed_102021: proof_shape=bind-only; consumers=row_counts
completed_102101: proof_shape=bind-only; consumers=row_counts
completed_102102: proof_shape=bind-only; consumers=row_counts
completed_102120: proof_shape=bind-only; consumers=row_counts
completed_102121: proof_shape=bind-only; consumers=row_counts
completed_120101: proof_shape=bind-only; consumers=row_counts
completed_120102: proof_shape=bind-only; consumers=row_counts
completed_120120: proof_shape=bind-only; consumers=row_counts
completed_120121: proof_shape=bind-only; consumers=row_counts
completed_120201: proof_shape=bind-only; consumers=row_counts
completed_120202: proof_shape=bind-only; consumers=row_counts
completed_120210: proof_shape=bind-only; consumers=row_counts
completed_120212: proof_shape=bind-only; consumers=row_counts
completed_121010: proof_shape=bind-only; consumers=row_counts
completed_121012: proof_shape=bind-only; consumers=row_counts
completed_121020: proof_shape=bind-only; consumers=row_counts
completed_121021: proof_shape=bind-only; consumers=row_counts
completed_121201: proof_shape=bind-only; consumers=row_counts
completed_121202: proof_shape=bind-only; consumers=row_counts
completed_121210: proof_shape=bind-only; consumers=row_counts
completed_121212: proof_shape=bind-only; consumers=row_counts
completed_201010: proof_shape=bind-only; consumers=row_counts
completed_201012: proof_shape=bind-only; consumers=row_counts
completed_201020: proof_shape=bind-only; consumers=row_counts
completed_201021: proof_shape=bind-only; consumers=row_counts
completed_201201: proof_shape=bind-only; consumers=row_counts
completed_201202: proof_shape=bind-only; consumers=row_counts
completed_201210: proof_shape=bind-only; consumers=row_counts
completed_201212: proof_shape=bind-only; consumers=row_counts
completed_202010: proof_shape=bind-only; consumers=row_counts
completed_202012: proof_shape=bind-only; consumers=row_counts
completed_202020: proof_shape=bind-only; consumers=row_counts
completed_202021: proof_shape=bind-only; consumers=row_counts
completed_202101: proof_shape=bind-only; consumers=row_counts
completed_202102: proof_shape=bind-only; consumers=row_counts
completed_202120: proof_shape=bind-only; consumers=row_counts
completed_202121: proof_shape=bind-only; consumers=row_counts
completed_210101: proof_shape=bind-only; consumers=row_counts
completed_210102: proof_shape=bind-only; consumers=row_counts
completed_210120: proof_shape=bind-only; consumers=row_counts
completed_210121: proof_shape=bind-only; consumers=row_counts
completed_210201: proof_shape=bind-only; consumers=row_counts
completed_210202: proof_shape=bind-only; consumers=row_counts
completed_210210: proof_shape=bind-only; consumers=row_counts
completed_210212: proof_shape=bind-only; consumers=row_counts
completed_212010: proof_shape=bind-only; consumers=row_counts
completed_212012: proof_shape=bind-only; consumers=row_counts
completed_212020: proof_shape=bind-only; consumers=row_counts
completed_212021: proof_shape=bind-only; consumers=row_counts
completed_212101: proof_shape=bind-only; consumers=row_counts
completed_212102: proof_shape=bind-only; consumers=row_counts
completed_212120: proof_shape=bind-only; consumers=row_counts
completed_212121: proof_shape=bind-only; consumers=row_counts
unseen_010101: proof_shape=bind-only; consumers=row_counts
unseen_101010: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_valid: proof_shape=bind-only; consumers=a_eq_w
first_fibres: proof_shape=bind-only; consumers=initial_counts
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w
w: proof_shape=bind-only; consumers=shifted_count
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=shifted_count
distribution: proof_shape=bind-only; consumers=distribution_step
distribution_step: proof_shape=bind-only; consumers=shifted_count
shifted_count: proof_shape=bind-only; consumers=result
distribution_relation: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result (#28649)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Literal six-column square-strip counts and their all-height class reduction. -/

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip
  (widthLegal widthV widthStep widthTotal width_counting_bridge colour_bond_iff)
open HardinA233254TriangleStrip (Row rowLegal)
open HardinA233255PairTransfer (Boundary)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 6, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

private instance decidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

/-- Literal filtered array count. The first-cell condition sets the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 6 → Fin 6 => widthLegal rowLegal bonds A)).card

def labels (c : Row) : Boundary := fun j => beta (c j)
def compatible (p : Boundary) (c : Row) : Prop := ∀ j, p j ≠ beta (c j)
private instance decidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible
private abbrev total := widthTotal rowLegal labels

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 5, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)

def boundaryClass (s : Seen) (p : Boundary) : Fin 11 :=
  if s.2 then
    if p 2 = p 0 then
      if p 3 = p 1 then
        if p 4 = p 2 then (if p 5 = p 3 then 1 else 2)
        else (if p 5 = p 3 then 4 else 3)
      else if p 4 = p 2 then (if p 5 = p 3 then 4 else 5)
        else (if p 5 = p 3 then 7 else 6)
    else if p 3 = p 1 then
      if p 4 = p 2 then (if p 5 = p 3 then 2 else 10)
      else (if p 5 = p 3 then 5 else 9)
    else if p 4 = p 2 then (if p 5 = p 3 then 3 else 9)
      else (if p 5 = p 3 then 6 else 8)
  else 0

def transfer (i k : Fin 11) : ℤ :=
  ![![64, 64, 128, 64, 128, 128, 0, 32, 0, 64, 32]
    , ![0, 192, 256, 128, 256, 256, 0, 64, 0, 128, 64]
    , ![0, 128, 256, 64, 192, 192, 64, 64, 0, 128, 64]
    , ![0, 64, 64, 192, 128, 64, 128, 64, 64, 64, 64]
    , ![0, 128, 192, 128, 256, 192, 64, 64, 0, 128, 64]
    , ![0, 128, 192, 64, 192, 256, 0, 64, 0, 128, 64]
    , ![0, 0, 64, 128, 64, 0, 192, 64, 64, 64, 64]
    , ![0, 64, 128, 128, 128, 128, 128, 128, 0, 128, 64]
    , ![0, 0, 0, 128, 0, 0, 128, 0, 128, 0, 64]
    , ![0, 64, 128, 64, 128, 128, 64, 64, 0, 192, 0]
    , ![0, 64, 128, 128, 128, 128, 128, 64, 64, 0, 128]] i k

private theorem valid_next (s : Seen) (c : Row)
    (hs : s.1 = true ∨ ∃ i, c i = 1) (hc : rowLegal c ∧ good s c) :
    Valid (finish s c) (labels c) := by
  refine ⟨HardinA233175PairStrip.finish_fst s c |>.mpr hs, ?_, ?_⟩
  · intro j
    exact (colour_bond_iff _ _).mp (hc.1 j)
  · intro ht j
    have htwo : ∀ i, c i ≠ 2 := by
      intro i hi
      have hh := (HardinA233175PairStrip.finish_snd s c).mpr (Or.inr ⟨i, hi⟩)
      simp [ht] at hh
    have hstate : s.2 ≠ true := by
      intro hi
      have hh := (HardinA233175PairStrip.finish_snd s c).mpr (Or.inl hi)
      simp [ht] at hh
    have hthree : ∀ i, c i ≠ 3 := by
      intro i hi
      rcases ((HardinA233175PairStrip.good_iff s c).mp hc.2 i).2 hi with
        hh | ⟨r, _, hr⟩
      · exact hstate hh
      · exact htwo r hr
    have hb : ∀ x : Fin 6, beta x = 2 ↔ x = 2 ∨ x = 3 := by decide +kernel
    intro hx
    rcases (hb _).mp hx with hh | hh
    · exact htwo _ hh
    · exact hthree _ hh

def classCount (s : Seen) (p : Boundary) (k : Fin 11) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (labels c) = k then 1 else 0

def firstCount (k : Fin 11) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0

private theorem class_fibres (s : Seen) (p : Boundary) (k : Fin 11) :
    classCount s p k = ∑ q : Boundary,
      rowWeight s q * if (∀ j : Fin 5, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 6 s (fun t q =>
    if (∀ j : Fin 5, q j.castSucc ≠ q j.succ) ∧
      (∀ j, p j ≠ q j) ∧ boundaryClass t q = k then (1 : ℤ) else 0)]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  simp only [← colour_bond_iff]
  change (if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) =
    if good s c then (if rowLegal c ∧ compatible p c ∧
      boundaryClass (finish s c) (labels c) = k then 1 else 0) else 0
  by_cases hg : good s c <;> simp [hg]

private theorem class_fibres_normalized (s : Seen) (p : Boundary) (k : Fin 11) :
    classCount s p k =
      ∑ q0 : Fin 3, ∑ q1 : Fin 3, ∑ q2 : Fin 3, ∑ q3 : Fin 3,
      ∑ q4 : Fin 3, ∑ q5 : Fin 3,
      rowWeight s ![q0, q1, q2, q3, q4, q5] *
      if (∀ j : Fin 5, (![q0, q1, q2, q3, q4, q5] : Boundary) j.castSucc ≠
        (![q0, q1, q2, q3, q4, q5] : Boundary) j.succ) ∧
        (∀ j : Fin 6, p j ≠ (![q0, q1, q2, q3, q4, q5] : Boundary) j) ∧
        boundaryClass (rowFinish s ![q0, q1, q2, q3, q4, q5])
          ![q0, q1, q2, q3, q4, q5] = k then 1 else 0 := by
  simp only [class_fibres]
  simp_rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 5 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin 3)).sum_comp,
    Fintype.sum_prod_type]
  simp [Fin.consEquiv, Matrix.empty_eq]

private theorem completed_010101 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010102 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010120 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010121 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010201 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010202 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010210 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_010212 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012010 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012012 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012020 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012021 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012101 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012102 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012120 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_012121 : ∀ k : Fin 11,
    classCount (true, true) ![0, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020101 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020102 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020120 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020121 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020201 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020202 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020210 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_020212 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021010 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021012 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021020 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021021 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021201 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021202 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021210 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_021212 : ∀ k : Fin 11,
    classCount (true, true) ![0, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![0, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101010 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101012 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101020 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101021 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101201 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101202 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101210 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_101212 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102010 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102012 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102020 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102021 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102101 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102102 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102120 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_102121 : ∀ k : Fin 11,
    classCount (true, true) ![1, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120101 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120102 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120120 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120121 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120201 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120202 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120210 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_120212 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121010 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121012 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121020 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121021 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121201 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121202 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121210 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_121212 : ∀ k : Fin 11,
    classCount (true, true) ![1, 2, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![1, 2, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201010 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201012 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201020 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201021 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201201 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201202 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201210 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_201212 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 1, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 1, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202010 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202012 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202020 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202021 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202101 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202102 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202120 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_202121 : ∀ k : Fin 11,
    classCount (true, true) ![2, 0, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 0, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210101 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210102 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210120 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210121 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210201 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210202 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210210 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_210212 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 0, 2, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 0, 2, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212010 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 1, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212012 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 1, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 1, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212020 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212021 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 0, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 0, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212101 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 0, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212102 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 0, 2] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 0, 2]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212120 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 2, 0] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 0]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem completed_212121 : ∀ k : Fin 11,
    classCount (true, true) ![2, 1, 2, 1, 2, 1] k =
      transfer (boundaryClass (true, true) ![2, 1, 2, 1, 2, 1]) k := by
  simp only [class_fibres_normalized,
    (HardinA233255ShapeSymmetry.full_row 6 _).1,
    (HardinA233255ShapeSymmetry.full_row 6 _).2]
  decide +kernel

private theorem unseen_010101 : ∀ k : Fin 11,
    classCount (true, false) ![0, 1, 0, 1, 0, 1] k =
      transfer (boundaryClass (true, false) ![0, 1, 0, 1, 0, 1]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

private theorem unseen_101010 : ∀ k : Fin 11,
    classCount (true, false) ![1, 0, 1, 0, 1, 0] k =
      transfer (boundaryClass (true, false) ![1, 0, 1, 0, 1, 0]) k := by
  simp only [class_fibres_normalized]
  decide +kernel

section
attribute [local irreducible] classCount

set_option maxHeartbeats 2000000 in
-- Exhaust the 98 legal boundaries after rejecting the other label rows.
private theorem row_counts : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rintro ⟨b1, b2⟩ p0 p1 p2 p3 p4 p5 hp k
  cases b1
  · cases hp.1
  · cases b2 <;> fin_cases p0 <;> fin_cases p1 <;>
      simp [Valid, Fin.forall_fin_succ] at hp
    all_goals fin_cases p2 <;> simp at hp
    all_goals fin_cases p3 <;> simp at hp
    all_goals fin_cases p4 <;> simp at hp
    all_goals fin_cases p5 <;> simp at hp
    all_goals first
      | exact completed_010101 k
      | exact completed_010102 k
      | exact completed_010120 k
      | exact completed_010121 k
      | exact completed_010201 k
      | exact completed_010202 k
      | exact completed_010210 k
      | exact completed_010212 k
      | exact completed_012010 k
      | exact completed_012012 k
      | exact completed_012020 k
      | exact completed_012021 k
      | exact completed_012101 k
      | exact completed_012102 k
      | exact completed_012120 k
      | exact completed_012121 k
      | exact completed_020101 k
      | exact completed_020102 k
      | exact completed_020120 k
      | exact completed_020121 k
      | exact completed_020201 k
      | exact completed_020202 k
      | exact completed_020210 k
      | exact completed_020212 k
      | exact completed_021010 k
      | exact completed_021012 k
      | exact completed_021020 k
      | exact completed_021021 k
      | exact completed_021201 k
      | exact completed_021202 k
      | exact completed_021210 k
      | exact completed_021212 k
      | exact completed_101010 k
      | exact completed_101012 k
      | exact completed_101020 k
      | exact completed_101021 k
      | exact completed_101201 k
      | exact completed_101202 k
      | exact completed_101210 k
      | exact completed_101212 k
      | exact completed_102010 k
      | exact completed_102012 k
      | exact completed_102020 k
      | exact completed_102021 k
      | exact completed_102101 k
      | exact completed_102102 k
      | exact completed_102120 k
      | exact completed_102121 k
      | exact completed_120101 k
      | exact completed_120102 k
      | exact completed_120120 k
      | exact completed_120121 k
      | exact completed_120201 k
      | exact completed_120202 k
      | exact completed_120210 k
      | exact completed_120212 k
      | exact completed_121010 k
      | exact completed_121012 k
      | exact completed_121020 k
      | exact completed_121021 k
      | exact completed_121201 k
      | exact completed_121202 k
      | exact completed_121210 k
      | exact completed_121212 k
      | exact completed_201010 k
      | exact completed_201012 k
      | exact completed_201020 k
      | exact completed_201021 k
      | exact completed_201201 k
      | exact completed_201202 k
      | exact completed_201210 k
      | exact completed_201212 k
      | exact completed_202010 k
      | exact completed_202012 k
      | exact completed_202020 k
      | exact completed_202021 k
      | exact completed_202101 k
      | exact completed_202102 k
      | exact completed_202120 k
      | exact completed_202121 k
      | exact completed_210101 k
      | exact completed_210102 k
      | exact completed_210120 k
      | exact completed_210121 k
      | exact completed_210201 k
      | exact completed_210202 k
      | exact completed_210210 k
      | exact completed_210212 k
      | exact completed_212010 k
      | exact completed_212012 k
      | exact completed_212020 k
      | exact completed_212021 k
      | exact completed_212101 k
      | exact completed_212102 k
      | exact completed_212120 k
      | exact completed_212121 k
      | exact unseen_010101 k
      | exact unseen_101010 k
end

private theorem initial_valid (c : Row)
    (hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c) :
    Valid (finish (false, false) c) (labels c) := by
  have hedge : (0 : Fin 6) ≠ c 1 ∧ (c 1).val ≠ 5 := by
    have hh := hc.2.1 (0 : Fin 5)
    change c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 5 at hh
    simpa only [hc.1, Fin.val_zero, zero_add] using hh
  have hcol : ∀ x : Fin 6, x ≠ 0 → x.val ≠ 5 → x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    decide +kernel
  have hone : ∃ i, c i = 1 := by
    rcases hcol _ (Ne.symm hedge.1) hedge.2 with hi | hi
    · exact ⟨1, hi⟩
    · rcases ((HardinA233175PairStrip.good_iff _ c).mp hc.2.2 1).1 hi with
        hh | ⟨i, _, hi⟩
      · cases hh
      · exact ⟨i, hi⟩
  exact valid_next _ c (Or.inr hone) ⟨hc.2.1, hc.2.2⟩

private theorem first_fibres (k : Fin 11) :
    firstCount k = ∑ q : Fin 5 → Fin 3, rowWeight (false, false) q *
      if (∀ j : Fin 5, (Fin.cons 0 q : Boundary) j.castSucc ≠
        (Fin.cons 0 q : Boundary) j.succ) ∧
        boundaryClass (rowFinish (false, false) q) (Fin.cons 0 q) = k then 1 else 0 := by
  unfold firstCount
  rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 6)).sum_comp, Fintype.sum_prod_type]
  change (∑ x : Fin 6, ∑ c : Fin 5 → Fin 6,
    if x = 0 ∧ rowLegal (Fin.cons x c) ∧ good (false, false) (Fin.cons x c) ∧
      boundaryClass (finish (false, false) (Fin.cons x c)) (labels (Fin.cons x c)) = k
      then (1 : ℤ) else 0) = _
  rw [Finset.sum_eq_single (0 : Fin 6)]
  · have hh := scanner_fibres 5 (false, false) (fun t q =>
      if (∀ j : Fin 5, (Fin.cons 0 q : Boundary) j.castSucc ≠
        (Fin.cons 0 q : Boundary) j.succ) ∧ boundaryClass t (Fin.cons 0 q) = k
        then (1 : ℤ) else 0)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro c _
    have hb : labels (Fin.cons 0 c) = Fin.cons 0 (fun j => beta (c j)) :=
      Fin.comp_cons beta 0 c
    have hg : good (false, false) (Fin.cons 0 c) ↔ good (false, false) c := by
      change (HardinA233175PairStrip.allowed (false, false) 0 ∧
        good (HardinA233175PairStrip.advance (false, false) 0) c) ↔ _
      simp only [show HardinA233175PairStrip.allowed (false, false) (0 : Fin 6) from
        by decide +kernel, show HardinA233175PairStrip.advance (false, false) (0 : Fin 6) =
          (false, false) from by decide +kernel, true_and]
    have hf : finish (false, false) (Fin.cons 0 c) = finish (false, false) c := rfl
    have hr : (∀ j : Fin 5,
        (Fin.cons 0 (fun i => beta (c i)) : Boundary) j.castSucc ≠
        (Fin.cons 0 (fun i => beta (c i)) : Boundary) j.succ) ↔
        rowLegal (Fin.cons 0 c) := by
      rw [← hb]
      simp only [labels, ← colour_bond_iff]
      rfl
    have hr' : (∀ j : Fin 5, labels (Fin.cons 0 c) j.castSucc ≠
        labels (Fin.cons 0 c) j.succ) ↔ rowLegal (Fin.cons 0 c) := by
      simpa only [hb] using hr
    simp only [eq_self, true_and, ← hb, hg, hf, hr']
    by_cases hc : good (false, false) c <;>
      simp only [hc, ↓reduceIte, true_and, and_false, false_and]
  · intro x _ hx
    simp [hx]
  · simp

private theorem initial_counts : ∀ k,
    firstCount k = ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k := by
  simp only [first_fibres]
  simp_rw [← (Fin.consEquiv (fun _ : Fin 5 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin 3)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv]
  decide +kernel

/-- The exact single-row transitions and first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 11 → ℤ
  | 0, _ => 1
  | n + 1, i => ∑ k : Fin 11, transfer i k * w n k

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (labels c) else 0) =
        ∑ k : Fin 11, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) * w n k := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s c (Or.inl h.1) ⟨hc.1, hc.2.2⟩)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k : Fin 11, classCount s p k * w n k) = _
    simp_rw [finite_certificate.1 s p h]
    rfl

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = ∑ k : Fin 11, ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k * w n k := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labels c) else 0) =
      ∑ k : Fin 11, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labels c) = k then (1 : ℤ) else 0) *
          w n k := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ k : Fin 11, firstCount k * w n k) = _
  simp_rw [finite_certificate.2]

private def distribution (r : Fin 9) (k : Fin 11) : ℤ :=
  ![![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8],
    ![1024, 10240, 18432, 14336, 19456, 17408, 11264, 8192, 3584, 13312, 7680],
    ![65536, 11894784, 19922944, 13697024, 20905984, 19136512, 9764864, 8257536, 2588672,
      13697024, 7602176],
    ![4194304, 12731809792, 21126709248, 13820231680, 22066233344, 20451426304, 9479127040,
      8522825728, 2319450112, 14390657024, 7769948160],
    ![268435456, 13439489540096, 22250346512384, 14285598097408, 23194970882048, 21600464273408,
      9656697094144, 8888569036800, 2285325254656, 15121506107392, 8067827630080],
    ![17179869184, 14129523280838656, 23375634386386944, 14905288863776768, 24350368624279552,
      22716013309067264, 10021859508617216, 9305227035410432, 2341169493180416,
      15875504796073984, 8431184010805248],
    ![1099511627776, 14834548759546822656, 24535730616681889792, 15605868810815406080,
      25552052095188729856, 23852115859181928448, 10472500808892022784, 9754613724198469632,
      2434602967651844096, 16659661645596852224, 8832477511238549504],
    ![70368744177664, 15567108237574814040064, 25744991932724816117760, 16360109272758489186304,
      26808812111241439870976, 25031000536475729133568, 10970884659964933046272,
      10230667782738877087744, 2545923396239978659840, 17479390576998738821120,
      9261247309720961679360],
    ![4503599627370496, 16332950328716430292287488, 27010652418350597978193920,
      17158719867507552292962304, 28125783903232205206323200, 26262820350752900696244224,
      11503471623921690059210752, 10731832335239811082223616, 2667781634235157838823424,
      18338196923878383063924736, 9714047525398103845765120]] r k

private theorem distribution_step : ∀ (r : Fin 8) (k : Fin 11),
    distribution r.succ k = ∑ i : Fin 11, distribution r.castSucc i * transfer i k := by
  decide +kernel

private theorem shifted_count (r : Fin 9) (n : ℕ) :
    (a (n + r.val + 1) : ℤ) = ∑ k : Fin 11, distribution r k * w n k := by
  induction r using Fin.induction generalizing n with
  | zero => exact a_eq_w n
  | succ r ih =>
    rw [show n + r.succ.val + 1 = (n + 1) + r.castSucc.val + 1 by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega, ih]
    simp only [w, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← distribution_step]

private theorem distribution_relation : ∀ k : Fin 11,
    distribution 8 k = 1984 * distribution 7 k -
      1314816 * distribution 6 k +
      411303936 * distribution 5 k -
      70111985664 * distribution 4 k +
      6893422510080 * distribution 3 k -
      389708152569856 * distribution 2 k +
      11733988091625472 * distribution 1 k -
      145241087982698496 * distribution 0 k := by
  decide +kernel

/-- Hardin's recurrence at every height at least nine, with the index shift explicit. -/
theorem result (n : ℕ) :
    (a (n + 9) : ℤ) = 1984 * a (n + 8) - 1314816 * a (n + 7) +
      411303936 * a (n + 6) - 70111985664 * a (n + 5) +
      6893422510080 * a (n + 4) - 389708152569856 * a (n + 3) +
      11733988091625472 * a (n + 2) - 145241087982698496 * a (n + 1) := by
  have h0 := shifted_count (0 : Fin 9) n
  have h1 := shifted_count (1 : Fin 9) n
  have h2 := shifted_count (2 : Fin 9) n
  have h3 := shifted_count (3 : Fin 9) n
  have h4 := shifted_count (4 : Fin 9) n
  have h5 := shifted_count (5 : Fin 9) n
  have h6 := shifted_count (6 : Fin 9) n
  have h7 := shifted_count (7 : Fin 9) n
  have h8 := shifted_count (8 : Fin 9) n
  change (a (n + 1) : ℤ) = _ at h0
  change (a (n + 2) : ℤ) = _ at h1
  change (a (n + 3) : ℤ) = _ at h2
  change (a (n + 4) : ℤ) = _ at h3
  change (a (n + 5) : ℤ) = _ at h4
  change (a (n + 6) : ℤ) = _ at h5
  change (a (n + 7) : ℤ) = _ at h6
  change (a (n + 8) : ℤ) = _ at h7
  change (a (n + 9) : ℤ) = _ at h8
  rw [h8, h7, h6, h5, h4, h3, h2, h1, h0]
  simp_rw [distribution_relation, sub_mul, add_mul]
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, Finset.mul_sum]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
