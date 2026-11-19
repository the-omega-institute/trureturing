using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation.FixedZeroObstruction;

internal sealed class LocalPureLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/FixedZeroObstruction/LocalPureLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local uniqueness of one original exclusion label controls the entire moving exclusion at an interior mixed limit.",
        H("Local single-label collapse"), Blocks(
            Describe.Lean(DescribeId.Create("exclusion-radius"), DeclarationHandle.Create(Owner + "exclusionRadius"),
                H("Whole-exclusion radius"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every ambient point p and actual original pure label r, exclusionRadius(p,r) is the real supremum of norm(x-p) over every x in the entire original exclusion(C,u,r). Under the compact positive-dimensional ball hypotheses the supremum is an attained nonnegative maximum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-single-label-collapse"), DeclarationHandle.Create(Owner + "local_single_label_collapse"),
                H("An interior limit collapses the whole returned ball"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite dimensional real normed space V, original pointed cone C and linear unit u, assume C is closed, u is strictly positive on every nonzero point of C, C spans V, and every original pure label has a positive-dimensional injective affine Euclidean closed-ball chart of its entire exclusion. Fix any original pure p for which every original pure s with D(s)=D(p) equals p. For every ambient y in intrinsicInterior(real,D(p)), every sequence rn of original pure points converging in V to y satisfies exclusionRadius(p,rn(n)) tending to zero. Ball dimensions may vary, the pure locus need not be closed, and no global injectivity of the exclusion map is assumed.")),
                    Paragraph(Text("Choose complete original zero confirmers along rn. Compactness of the entire original effect interval gives one effect limit e with e(y)=1 and e(x)=0 at any convergent selection x from the moving exclusions. The frozen zero_on_exclusion_of_zero_interior theorem, applied to u-e, forces e to equal one on all D(p). Choose two distinct original pure points a,a' of D(p). The frozen single_label_neighbor theorem gives local uniqueness at a. Both x and p lie in D(a) and D(a'); if x differs from p, the frozen equal_of_two_points theorem identifies those two balls, contradicting the distinct locally unique labels. Compactness then forces every maximizing selection to converge to p, proving the maximum statement.")),
                    Paragraph(Text("This is a conditional geometric result in the entire original cone domain. It supplies no existence of a pure sequence approaching y, no local pure-limit principle, no positive-lift existence, and no empirical or historical novelty claim. The source-bound Reg mirror checks the complete original telescope and actual law; a lawful four-slot registration additionally requires whole-family variation and observational sensitivity."))), DescribeRole.Theorem))));
}
