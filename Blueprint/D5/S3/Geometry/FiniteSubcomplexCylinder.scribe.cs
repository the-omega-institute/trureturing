using System;
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteSubcomplexCylinderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteSubcomplexCylinder.";
    private const string OwnerHeader = """
        /- GID: D5/S3/Geometry/FiniteSubcomplexCylinder
           generality: G
           mirror-B: D5/B/S3/Geometry/FiniteSubcomplexCylinder
           mirror-E: none(waiver:finite-subcomplex-cylinder)
           anchors: [mathlib/module/Mathlib.Topology.Compactness.Compact, mathlib/module/Mathlib.Topology.Piecewise]
           utility: none
           digest: A coordinate collar retracts the entire bottom-or-subcomplex cylinder and gives arbitrary-target homotopy extension. -/
        """;

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteSubcomplexCylinder",
            "A coordinate collar retracts the entire bottom-or-subcomplex cylinder and gives arbitrary-target homotopy extension.",
            "finite-subcomplex-cylinder",
            [Anchor.ParseCanonical("mathlib/module/Mathlib.Topology.Compactness.Compact"),
             Anchor.ParseCanonical("mathlib/module/Mathlib.Topology.Piecewise")]),
        H("Whole subcomplex cylinder and homotopy extension"),
        Blocks(
            SourceText(OwnerHeader),
            SourceText("The paired Lean module supplies these definitions and proofs."),
            SourceText("The authored context is variable {V : Type*} [Fintype V] [DecidableEq V]. The section NonemptyFaces uses P : SubcomplexPair V, whose nonempty face collection is genuinely required for its minimum. Outside that section K and L are arbitrary complexes; Extension adds only {Y : Type*} [TopologicalSpace Y], f and g of the displayed types. No global nonempty label, full-subcomplex, cone, supplied collar, cofibration or extension assumption is inserted."),
            SourceText("The dependency FiniteConeCollapse.SubcomplexPair supplies the actual original-coordinate deformation. FiniteConeUnionWedge.realization_closed supplies closedness for the boundary pasting. These are reused definitions and theorems, not additional hypotheses of the final extension theorem."),
            SourceText("Actual consumer: D5.S3.Geometry.FiniteComponentClosure.contractible_cover_equivalence, defined in FiniteComponentClosure/ConeSplits.lean, constructs R and hR directly with retraction (X ⊔ Y) C hC and retraction_fixed, then supplies them to FiniteConeUnionWedge.contractibleCollapse. Its contractibility and basepoint assumptions belong to that consumer. The cylinder and arbitrary-target extension here require none of those assumptions. The import alone is not the evidence of use."),
            Node("space", "Space",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.Space",
                "The existing coordinate realization as a space",
                "Space K is the subtype of FiniteConeCollapse.realization K in V → ℝ with its inherited topology. The finite label type may be empty; no Nonempty V or chosen vertex is imposed by this abbreviation.",
                "abbrev Space (K : PreAbstractSimplicialComplex V)", DescribeRole.Definition),
            Node("subspace", "Subspace",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace",
                "The original realized subcomplex inside K",
                "Subspace K L consists of x : Space K whose unchanged coordinate vector belongs to realization L. This definition itself is meaningful without L ≤ K; the retraction and extension theorems supply that inclusion explicitly.",
                "def Subspace (K L : PreAbstractSimplicialComplex V) : Set (Space K)", DescribeRole.Definition),
            Node("cylinder", "Cylinder",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.Cylinder",
                "The whole bottom-or-subcomplex cylinder",
                "Cylinder K L is the set of pairs in Space K × I satisfying t=0 or x.val ∈ realization L; its coerced subtype is the retraction target. It contains the entire ambient bottom and the entire vertical cylinder over the realized subcomplex, rather than a selected-point cylinder or a collar-only subset.",
                "def Cylinder (K L : PreAbstractSimplicialComplex V) : Set (Space K × I)", DescribeRole.Definition),
            Node("realization-nonempty-iff-faces-nonempty", "realization_nonempty_iff_faces_nonempty",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.realization_nonempty_iff_faces_nonempty",
                "Face nonemptiness exactly detects points",
                "A realization point has a face witness. Conversely a face witness is a nonempty Mathlib face, so choose a vertex of that face and use its coordinate unit vector in the convex hull. No inhabitant of V is assumed in advance; this equivalence also handles an empty label type.",
                "theorem realization_nonempty_iff_faces_nonempty (L : PreAbstractSimplicialComplex V) :\n    (realization L).Nonempty ↔ (L : Set (Finset V)).Nonempty", DescribeRole.Theorem),
            Node("realization-eq-empty-of-no-faces", "realization_eq_empty_of_no_faces",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.realization_eq_empty_of_no_faces",
                "No faces gives the empty realization",
                "If L has no faces, any supposed realization point would yield a face by the previous equivalence, a contradiction. This empty-subcomplex branch needs neither a face minimum nor a point of L.",
                "theorem realization_eq_empty_of_no_faces (L : PreAbstractSimplicialComplex V)\n    (hL : ¬ (L : Set (Finset V)).Nonempty) : realization L = ∅", DescribeRole.Theorem),
            Node("control", "control",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.control",
                "The bounded original collar control",
                "For P : FiniteConeCollapse.SubcomplexPair V, control(x) is min(delta(x) / epsilon, 1) in I. Here outsideMass(s,x) is the sum of x(v) over the original labels v outside s; delta is its minimum over all actual subcomplex faces, and epsilon = 1 / (2 * (card V + 1)). The dependency proves delta ≥ 0, epsilon > 0, continuity, and delta=0 exactly on the realized subcomplex. At parameter s its deformation coordinate is max(x(v) - s * min(delta, epsilon), 0) divided by the sum of those truncated coordinates over V, a denominator at least 1/2. This preserves every original face and every zero ghost coordinate. Thus deform 1 enters the subcomplex when delta ≤ epsilon; control < 1 supplies this bound without assuming a collar.",
                "def control (x : P.Space) : I", DescribeRole.Definition),
            Node("nonempty-retraction", "nonemptyRetraction",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction",
                "The original collar retracts the full cylinder",
                "For a SubcomplexPair with an inhabited face collection, put u=control(x), choose time=min(t/u,1), and return (deform time x, max(t - control(x), 0)). Lean division at u=0 is defined as zero; the selector need not be continuous there. At u>0 the ratio and clamping are continuous. At u=0 the base point lies in the subcomplex and deform fixes it for every parameter. The compact interval and the generalized tube lemma give uniform neighborhood control for every selected time, so the horizontal composite is continuous at each zero-control point without any continuity of the selector there. Away from that locus, the particular ratio selector is continuous. Positive height forces t>u and hence either the fixed u=0 case or deform 1 with u<1; therefore the output lies in the whole bottom-or-subcomplex cylinder. This includes the u=1,t=1 corner without division by 1-u.",
                "def nonemptyRetraction : C(P.Space × I, Cylinder P.ambient P.subcomplex)", DescribeRole.Definition),
            Node("nonempty-retraction-lower", "nonemptyRetraction_lower",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_lower",
                "The lower branch including its seam",
                "Assume 0 < control(x) and t ≤ control(x). The clamped time is exactly t/control(x) in I and the height is zero. At equality t=control(x), the bounded ratio is one and both branch expressions agree as (deform 1 x, 0). The theorem keeps its positive-control hypothesis; it does not divide at zero.",
                "theorem nonemptyRetraction_lower (x : P.Space) (t : I)\n    (hx : 0 < (control P x : ℝ)) (ht : (t : ℝ) ≤ (control P x : ℝ)) :\n    (nonemptyRetraction P (x, t)).val =\n      (P.deform ⟨(t : ℝ) / (control P x : ℝ),\n        div_nonneg t.property.1 hx.le, (div_le_one hx).mpr ht⟩ x, 0)", DescribeRole.Theorem),
            Node("nonempty-retraction-upper", "nonemptyRetraction_upper",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_upper",
                "The upper branch has no height rescaling",
                "Assume 0 < control(x) and control(x) < t. The clamped time equals one, and the new height is the unnormalized difference t-control(x). Since t≤1, this strict inequality also gives control(x)<1, so deform 1 x lies in the subcomplex. No division by 1-control(x) or rational surrogate height is introduced.",
                "theorem nonemptyRetraction_upper (x : P.Space) (t : I)\n    (hx : 0 < (control P x : ℝ)) (ht : (control P x : ℝ) < (t : ℝ)) :\n    (nonemptyRetraction P (x, t)).val =\n      (P.deform 1 x, ⟨(t : ℝ) - (control P x : ℝ), sub_nonneg.mpr ht.le,\n        (sub_le_self _ hx.le).trans t.property.2⟩)", DescribeRole.Theorem),
            Node("nonempty-retraction-fixed", "nonemptyRetraction_fixed",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_fixed",
                "Every point of both cylinder pieces is fixed",
                "If the input is on the bottom, time at t=0 is zero and the deformation starts at x, while max(0-u,0)=0. If the base belongs to the subcomplex, u=0, every deformation time fixes x and max(t,0)=t. The disjunction proves exact fixedness on the entire target, including their intersection.",
                "theorem nonemptyRetraction_fixed (z : P.Space × I)\n    (hz : z.2 = 0 ∨ z.1.val ∈ realization P.subcomplex) :\n    (nonemptyRetraction P z).val = z", DescribeRole.Theorem),
            Node("retraction", "retraction",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.retraction",
                "A retraction for every finite inclusion",
                "Given hLK : L ≤ K, split on whether L has an actual face. The inhabited-face branch uses the displayed lower and upper formulas at positive control and nonemptyRetraction at zero control, for the exact pair (K,L,hLK,hL). Their proved equalities transport the joint continuity of nonemptyRetraction to this same map. When L has no faces, send (x,t) directly to (x,0). This formula uses no minimum or chosen point of L. Empty labels, empty K, empty L and ghost labels are allowed. If L=K, the target is all of Space K × I and the fixedness theorem makes the retraction identity.",
                "def retraction (hLK : L ≤ K) : C(Space K × I, Cylinder K L)", DescribeRole.Definition),
            Node("retraction-fixed", "retraction_fixed",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.retraction_fixed",
                "The unrestricted retraction fixes its whole target",
                "In the inhabited-face branch use branchRetraction_eq and nonemptyRetraction_fixed. In the no-faces branch, the side alternative is impossible because realization L is empty, and the bottom alternative is fixed by the bottom map. The exact equality is of the output value with the original pair, for every point satisfying either target condition.",
                "theorem retraction_fixed (hLK : L ≤ K) (z : Space K × I)\n    (hz : z.2 = 0 ∨ z.1.val ∈ realization L) : (retraction K L hLK z).val = z", DescribeRole.Theorem),
            Node("homotopy-extension", "homotopy_extension",
                "D5.S3.Geometry.FiniteSubcomplexCylinder.homotopy_extension",
                "Arbitrary-target homotopy extension",
                "For an arbitrary topological target Y, continuous f : Space K → Y and g : I × Subspace K L → Y, assume only g(0,a)=f(a.val) and L ≤ K. Define the boundary map on Cylinder by g on the side and f otherwise. The closed bottom and side cover the target: finite-coordinate realization_closed makes the side closed, and the time-zero condition makes the bottom closed. The two restrictions agree at the intersection by hzero, so closed pasting proves continuity with no separation axiom on Y. Compose this map with retraction and swap the time/base factors to obtain F : C(I × Space K,Y). Whole-target fixedness gives both the initial equality and the equality with g at every time on the subspace. HEP is a conclusion of the construction, not an input.",
                "theorem homotopy_extension (hLK : L ≤ K)\n    (hzero : ∀ a : Subspace K L, g (0, a) = f a.val) :\n    ∃ F : C(I × Space K, Y), (∀ x, F (0, x) = f x) ∧\n      ∀ (t : I) (a : Subspace K L), F (t, a.val) = g (t, a)", DescribeRole.Theorem))));

    // The pinned SDK has Create, not FromLeanNames. Every leaf selector below is
    // bound to its exact source namespace above; native unique-suffix resolution is still due.
    private static DocumentBlock Node(string id, string selector, string leanName,
        string title, string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose), SourceText("Lean name:" + leanName),
                SourceText("Exact authored Lean header:" + rawContract)), role);

    // Preserve decoded multiline quotations using one valid TextRun per source line.
    // Quotations are commentary; theorem statements must come from Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
