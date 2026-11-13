using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class CommonSourceLiftObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/CommonSourceLiftObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local singleton exclusion label controls the entire moving exclusion near every relative interior point of its original ball.",
        H("Local limits of whole original exclusions"), Blocks(
        Paragraph(Text("Keep an arbitrary finite dimensional real normed space, the entire closed generating cone C, a strictly positive linear unit u, its whole normalized base K, all its extreme points P, and the entire original interval of effects. Each complete original exclusion has an injective affine chart of a positive dimensional Euclidean ball. Dimensions may vary and segments are included. The singleton label condition is imposed only at the specified original p. Distances use the supplied original norm.")),
        Describe.Lean(DescribeId.Create("single-label-mixed-upper-limit"),
            DeclarationHandle.Create(Owner + "single_label_mixed_upper_limit"),
            H("Every exclusion cluster point equals the original label"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let y be in the relative interior of F=D(p). If original pure labels r(n) converge to y, and any states x(n) in their complete exclusions converge to x, then x=p. Compactness of the full effect interval supplies a common limiting confirmer with value one on all of F and zero at x. Choose two distinct original pure sphere points a,b in F. Local singleton propagation makes their exclusion balls different. Both balls contain p and x, so two-point face rigidity forces x=p. This argument uses no global injectivity and makes no assertion that such a pure sequence exists."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("single-label-mixed-shrinking"),
            DeclarationHandle.Create(Owner + "single_label_mixed_shrinking"),
            H("Entire exclusions shrink uniformly to p"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For the same hypothetical sequence and every positive epsilon, all states in D(r(n)) eventually have original distance less than epsilon from p. A violation selects states a fixed positive distance away. Compactness of the whole original K supplies a cluster point, and the preceding conclusion identifies it with p. The quantifier covers every mixed state of each entire exclusion, not only a selected pure return label."))),
            DescribeRole.Theorem),
        Paragraph(Text("The conclusions are conditional on the original sequence. They establish neither its existence nor any positive extension or local openness assertion. They do not impose a common dimension, a closed pure locus, a distinguished effect, or an inner product on the ambient space.")))));
}
