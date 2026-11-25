using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class CenterOutwardTripleMonomialDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "CenterOutwardTripleMonomial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common-radius three-center Laurent obstruction",
        H("The common-radius three-center Laurent obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("center-laurent-single-active-reduction"),
                DeclarationHandle.Create(Module + ".closed_triple_laurent_single_active"),
                H("Weight transport and energy ratios force single-active private support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three private coordinate blocks are relative to the "
                        + "coordinatewise majority center. Matching row exponents "
                        + "fixes the bits in each residual's own block, and closure "
                        + "forces those bits to be opposite its center. The common exact "
                        + "sphere radius rules out a missing private block.")),
                    Paragraph(Text(
                        "The shared-row energies have ratios determined by the sums "
                        + "of squared weights on the private blocks. After factoring "
                        + "out the common Laurent shift, scale one block using weights "
                        + "one, two and four. The resulting moment identities give zero "
                        + "weighted variance, forcing exactly one active private coordinate "
                        + "in every nonzero shared row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-three-laurent-contradiction"),
                DeclarationHandle.Create(Module + ".closed_triple_laurent_false"),
                H("Three nonzero closed residuals with matching exponents are impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three-center support reduction gives the hypotheses "
                        + "of the single-active curvature theorem. Its signed square "
                        + "relations contradict nonzero residuals. The proof works "
                        + "with arbitrary real residual coefficients.")),
                    Paragraph(Text(
                        "For common-radius pieces of the two-contact monomial kernel "
                        + "in Hong, Wu and Xia's Problem 2, this supplies the "
                        + "algebraic three-piece obstruction. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "CenterOutwardTripleCurvature")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "CenterOutwardDifference")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "CenterOutwardWeightGauge"))
        ]));
}
