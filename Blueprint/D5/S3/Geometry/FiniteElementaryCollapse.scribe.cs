using System;
using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteElementaryCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteElementaryCollapse.";
    private const string OwnerHeader = """
        /- GID: D5/S3/Geometry/FiniteElementaryCollapse
           generality: G
           mirror-B: D5/B/S3/Geometry/FiniteElementaryCollapse
           mirror-E: none(waiver:finite-elementary-collapse)
           anchors: [mathlib/module/Mathlib.Data.Finset.Lattice.Fold, mathlib/module/Mathlib.Topology.Order.Lattice]
           utility: none
           digest: An explicit coordinate free-face deformation fixes the entire retained realization on the original labels. -/
        """;

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteElementaryCollapse",
            "An explicit coordinate free-face deformation fixes the entire retained realization on the original labels.",
            "finite-elementary-collapse",
            [Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Finset.Lattice.Fold"),
             Anchor.ParseCanonical("mathlib/module/Mathlib.Topology.Order.Lattice")]),
        H("Finite original-label elementary collapse"),
        Blocks(
            SourceText(OwnerHeader),
            SourceText("Let V be a finite type with decidable equality, and let P : CollapsePair V. A point is a nonnegative vector of total mass one supported on an actual nonempty face. Ghost labels remain coordinates with value zero, not extra vertices."),
            SourceText("The barycentric construction follows section 2 of the relative-cancellation proof, source SHA256 f9888966c4313557587f6c91f7a185a8aa6de6473219536205db6600e64553ad, which credits the cancellation proposal. The result here is the local elementary deformation; neither a link-collapse sequence nor theta cancellation is asserted."),
            Node("collapse-pair", "CollapsePair",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair",
                "A genuine free pair",
                "CollapsePair stores only an ambient nonempty-face complex, a nonempty lower face, an apex outside it, the upper-face membership, and the sole strict coface condition. Freeness is quantified over every ambient face; no realization, retraction, equivalence, or desired conclusion is a field. Finite original labels may include ghosts, and no purity or connectedness assumption is added.",
                "structure CollapsePair (V : Type*) [Fintype V] [DecidableEq V] where\n  ambient : PreAbstractSimplicialComplex V\n  lower : Finset V\n  apex : V\n  lower_nonempty : lower.Nonempty\n  apex_notMem : apex ∉ lower\n  upper_mem : insert apex lower ∈ ambient\n  free : ∀ s ∈ ambient, lower ⊂ s → s = insert apex lower", DescribeRole.Definition),
            Field("pair-ambient", "ambient",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.ambient",
                "Original ambient complex",
                "The ambient projection returns the given PreAbstractSimplicialComplex V. All coordinates, faces and subsequent retained complexes use this same V, including ghost labels.",
                "ambient : PreAbstractSimplicialComplex V"),
            Field("pair-lower", "lower",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.lower",
                "The designated lower face",
                "The lower projection returns the finite set used by freeness, the minimum and deletion. Its actual nonemptiness is recorded separately by lower_nonempty; it is never replaced by an augmented empty face.",
                "lower : Finset V"),
            Field("pair-apex", "apex",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.apex",
                "The original apex label",
                "The apex projection returns a label of the same V, not a fresh tag or a point in a changed realization. The apex_notMem field and upper_mem determine its role in the mass transfer.",
                "apex : V"),
            Field("pair-lower-nonempty", "lower_nonempty",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.lower_nonempty",
                "Nonempty lower-face evidence",
                "This proof-valued structure field supplies lower.Nonempty. It licenses the finite attained minimum.",
                "lower_nonempty : lower.Nonempty"),
            Field("pair-apex-not-mem", "apex_notMem",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.apex_notMem",
                "Disjoint mass-transfer coordinates",
                "This proof-valued field records apex ∉ lower. It ensures the apex receives all removed mass without also being one of the subtracted coordinates, and the attaining lower label is different from the apex.",
                "apex_notMem : apex ∉ lower"),
            Field("pair-upper-mem", "upper_mem",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.upper_mem",
                "The actual upper simplex exists",
                "This proof-valued field is membership of insert apex lower in ambient. It supplies the containing simplex for every active intermediate point, even when the original lower face has zero apex coordinate.",
                "upper_mem : insert apex lower ∈ ambient"),
            Field("pair-free", "free",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.free",
                "Every strict coface is the specified upper",
                "For each ambient s, lower ⊂ s implies s = insert apex lower. This is purely combinatorial freeness, used both to identify the exact deleted faces and to keep the deformation inside upper. It assumes no topological result.",
                "free : ∀ s ∈ ambient, lower ⊂ s → s = insert apex lower"),
            Node("upper", "upper",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.upper",
                "The exact upper face",
                "upper is insert apex lower on the original labels. The apex is outside lower, so these are distinct nonempty faces, with one additional vertex upstairs. This abbreviation introduces no replacement carrier.",
                "abbrev upper : Finset V", DescribeRole.Definition),
            Node("lower-mem", "lower_mem",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.lower_mem",
                "Lower-face membership from downward closure",
                "The inclusion lower ⊆ insert apex lower and lower_nonempty let the ambient relative lower-set law derive lower membership from upper_mem. No separate lower-face assumption is required.",
                "theorem lower_mem : P.lower ∈ P.ambient", DescribeRole.Theorem),
            Node("retained", "retained",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retained",
                "The literal retained complex",
                "The retained faces are exactly those s in ambient for which lower is not a subset of s. This family is closed under nonempty subfaces because any lower subset of a smaller face would also be a subset of the larger face. It retains all other faces and components on the same original labels. For every s t : Finset V, if hs : s ∈ P.retained, hts : t ⊆ s and ht : t.Nonempty, then t ∈ P.retained directly by (P.retained.isRelLowerSet_faces hs).2 hts ht. The nonempty hypothesis is essential: the empty face is never inserted into the geometric complex.",
                "def retained : PreAbstractSimplicialComplex V", DescribeRole.Definition),
            Node("mem-retained-iff", "mem_retained_iff",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.mem_retained_iff",
                "Exactly two faces are removed",
                "For each s, retained membership is equivalent to ambient membership with s unequal to lower and upper. To prove the converse, an ambient face containing lower is either lower itself or, by freeness when strict, upper. Thus the definition does not accidentally delete additional cofaces.",
                "theorem mem_retained_iff (s : Finset V) :\n    s ∈ P.retained ↔ s ∈ P.ambient ∧ s ≠ P.lower ∧ s ≠ P.upper", DescribeRole.Theorem),
            Node("retained-le", "retained_le",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retained_le",
                "The actual subcomplex inclusion",
                "Every retained face is an ambient face by its first conjunct. This is the order proof used to form the literal realizationInclusion, rather than an unrelated embedding of a homeomorphic space.",
                "theorem retained_le : P.retained ≤ P.ambient", DescribeRole.Theorem),
            Node("retained-nonempty", "retained_nonempty",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retained_nonempty",
                "Every retained face remains nonempty",
                "The nonempty-face axiom of the retained PreAbstractSimplicialComplex supplies s.Nonempty for every retained member. This theorem does not assert that the whole retained face collection or its realization is inhabited.",
                "theorem retained_nonempty {s : Finset V} (hs : s ∈ P.retained) : s.Nonempty", DescribeRole.Theorem),
            Node("empty-not-mem-retained", "empty_not_mem_retained",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.empty_not_mem_retained",
                "No geometric empty face",
                "An alleged empty retained face contradicts retained_nonempty. There is no augmented empty-face point and no default inhabitant of the label type.",
                "@[simp] theorem empty_not_mem_retained : (∅ : Finset V) ∉ P.retained", DescribeRole.Theorem),
            Node("minimum", "minimum",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.minimum",
                "The attained lower-face minimum",
                "minimum(x) is the infimum over the genuinely nonempty finite set lower, taken at the original lower labels only. For a probability vector it is nonnegative and no larger than any lower coordinate; an attaining label exists. On a retained face, a missing lower label has coordinate zero, forcing the minimum to vanish. No ambient ghost is added to the minimum.",
                "def minimum (x : V → ℝ) : ℝ", DescribeRole.Definition),
            Node("endpoint", "endpoint",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.endpoint",
                "Mass transfer to the original apex",
                "At the endpoint, subtract minimum(x) at every lower vertex and add lower.card * minimum(x) at the apex; every other coordinate stays x(v). The disjointness apex ∉ lower prevents overlap between those operations. Nonnegativity follows from the minimum bound, and the removed total mass is exactly the mass added. This global formula has no normalization denominator. For a singleton lower it transfers that single coordinate to the apex.",
                "def endpoint (x : V → ℝ) (v : V) : ℝ", DescribeRole.Definition),
            Node("endpoint-mem-retained", "endpoint_mem_retained",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.endpoint_mem_retained",
                "An endpoint in the exact retained realization",
                "Choose an ambient face witnessing x. If it contains lower, freeness puts it inside upper, and the whole straight segment stays in that upper simplex; otherwise the minimum is zero and x is fixed. First, mix_mem_ambient at t=1 puts the endpoint in the ambient realization. Obtain a new ambient face witnessing this endpoint, not necessarily the input face. The endpoint probability vector has support contained in this fresh face and nonempty by total mass one; downward closure therefore makes that support an ambient face. A lower label attaining the minimum has endpoint coordinate zero because it is not the apex, so the support omits a lower label and is an actual retained face. This includes an input face equal to the removed lower face, even when the apex coordinate starts zero. The target is the exact retained realization, not a homotopy-equivalent substitute.",
                "theorem endpoint_mem_retained (x : Space P.ambient) :\n    P.endpoint x.val ∈ realization P.retained", DescribeRole.Theorem),
            Node("inclusion", "inclusion",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.inclusion",
                "Unchanged coordinate inclusion",
                "inclusion is FiniteConeUnionWedge.realizationInclusion retained_le. It simply keeps the vector in V → ℝ with a larger membership proof, including the same zero coordinates at ghost labels.",
                "abbrev inclusion : C(Space P.retained, Space P.ambient)", DescribeRole.Definition),
            Node("retraction", "retraction",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retraction",
                "The continuous coordinate retraction",
                "Equip endpoint(x.val) with endpoint_mem_retained to define the map to Space retained. The finite minimum is continuous, and each fixed-label coordinate uses only addition, subtraction and constant multiplication, proving continuity before restriction to the actual subspaces.",
                "def retraction : C(Space P.ambient, Space P.retained)", DescribeRole.Definition),
            Node("retraction-inclusion", "retraction_inclusion",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retraction_inclusion",
                "All retained points are fixed",
                "For every y in the full retained realization, choose its retained face witness. Some lower vertex is missing, so minimum(y)=0 and endpoint(y)=y. Subtype extensionality gives retraction(inclusion(y))=y. This fixes all retained points, including additional components; it is not only a vertex equation.",
                "theorem retraction_inclusion (y : Space P.retained) :\n    P.retraction (P.inclusion y) = y", DescribeRole.Theorem),
            Node("collapse-homotopy", "collapseHomotopy",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.collapseHomotopy",
                "Strong deformation relative to the whole retained space",
                "The straight homotopy runs from identity to inclusion.comp retraction. If a witnessing face contains lower, its vertices lie in upper by the free-pair cases; both endpoints and their convex segment lie in the upper simplex. If it misses a lower label, minimum(x)=0 and the segment is constant. The relative condition uses this second argument for every ambient point already in the retained realization, at every time. For every t : I, x : Space P.ambient and v : V, (P.collapseHomotopy (t, x)).val v = x.val v + (if v = P.apex then (t : ℝ) * (P.lower.card : ℝ) * P.minimum x.val else 0) - (if v ∈ P.lower then (t : ℝ) * P.minimum x.val else 0). Both conditionals use the fixed original labels, independently of any chosen face witness. This equality follows directly by changing the left side to mix t x.val (P.endpoint x.val) v, unfolding mix and endpoint, and ring normalization in every conditional case; it holds globally, including t=0 and t=1.",
                "def collapseHomotopy :\n    (ContinuousMap.id (Space P.ambient)).HomotopyRel\n      (P.inclusion.comp P.retraction)\n      {x | x.val ∈ realization P.retained}", DescribeRole.Definition),
            Node("collapse-equiv", "collapseEquiv",
                "D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.collapseEquiv",
                "The actual inclusion is the inverse",
                "The forward map is retraction and the inverse is inclusion. The left inverse up to homotopy uses the reverse of collapseHomotopy; the right composite is exactly identity by retraction_inclusion. This packages the explicit relative deformation without changing coordinates or assuming an abstract equivalence.",
                "def collapseEquiv : Space P.ambient ≃ₕ Space P.retained", DescribeRole.Definition))));

    // Authored contracts accompany declarations outside the pinned projection corpus.
    private static DocumentBlock Node(string id, string selector, string leanName,
        string title, string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose), SourceText("Lean name: " + leanName),
                SourceText("Exact authored Lean header: " + rawContract)), role);

    // Field projections are referenced as declaration remarks.
    private static DocumentBlock Field(string id, string selector, string leanName,
        string title, string prose, string rawContract) => Describe.Remark(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose), SourceText("Lean name: " + leanName),
                SourceText("Exact authored Lean field: " + rawContract)));

    // Preserve decoded multiline quotations using one valid TextRun per source line.
    // Authored quotations are exposition; declaration handles identify the Lean source.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? " " : line)))))
        : Paragraph(Text(value));
}
