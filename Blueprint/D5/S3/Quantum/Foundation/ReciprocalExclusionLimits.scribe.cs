using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ReciprocalExclusionLimitsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ReciprocalExclusionLimits.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure reciprocity leaves exactly the whole old exclusion ball and pure singleton limits.",
        H("Whole original exclusion limits"), Blocks(
        Describe.Lean(DescribeId.Create("entire-three-ball-hypothesis"),
            DeclarationHandle.Create(Owner + "threeBallExclusions"), H("The original EB3 hypothesis"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("V is an arbitrary finite dimensional real normed space. C is the same original pointed cone and u the original strictly positive unit. K is the entire normalized base and P all its extreme points. For each original pure label, threeBallExclusions requires an injective affine map from Euclidean three-space whose entire closed unit ball image is the actual full exclusion D_p. The ambient dimension is not fixed. The continuous dual represents every original linear effect in finite dimension.")))),
        Describe.Lean(DescribeId.Create("whole-or-pure-singleton"),
            DeclarationHandle.Create(Owner + "exclusion_limit_dichotomy"),
            H("The exact whole-ball or pure-singleton alternative"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Assume C is closed and generating, u is strictly positive on nonzero cone vectors, EB3 holds, and the original full-effect comparison is reciprocal on all original pure endpoint pairs. Let a_n tend to a pure p. Let F_n be the complete D_a_n and let Q be any nonempty compact Hausdorff limit of these entire sets. Then Q equals D_p, or Q is the singleton of an original pure point q in D_p. This is the exact alternative of IX115.5. It supplies no global noncollapse, lower continuity, faithful labeling, least effect, weak-pair condition, or exclusion of the singleton branch.")),
            Paragraph(Text("The original parameter_subsequence owner extracts converging affine chart centers and continuous linear parts. recover_limit and exclusion_upper_limit put every point of Q in D_p. The PR-only reciprocal_pure_compact theorem keeps every limiting sphere point in the original pure locus. The original sphere_extreme_injective_or_zero theorem then makes the limiting operator injective or zero. In the zero case any unit sphere point proves that the singleton center is pure. In the injective case, the same-dimensional entire extreme sphere rigidity theorem eq_of_subset_of_extreme_sphere identifies the contained limit ball with D_p. No Hausdorff limit of faces is assumed to be a face.")),
            Paragraph(Text("The equality step consumes the original Geometry/AffineBallRigidity owner. Chart-parameter compactness, the rank lemma, upper association and the generic rigidity result are reused. The cross-label inference uses PR only through compactness of the complete original pure locus. All compact sets and maps retain the original carrier topology. This is a mathematical consequence of the declared original hypotheses, without a claim of physical reconstruction or literature priority."))), DescribeRole.Theorem)
        )));
}
