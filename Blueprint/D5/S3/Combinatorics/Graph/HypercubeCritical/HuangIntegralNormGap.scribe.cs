using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class HuangIntegralNormGapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive Huang energy of an integer vector on Q9 is at least three.",
        H("An integral energy gap for the original Huang matrix"),
        Blocks(
            Paragraph(Text(
                "This is a necessary structural ingredient for the Q9 cut bound. "
                    + "The original f₂(Q₉) problem remains unresolved; the existing "
                    + "48- and 96-vertex bounds do not exclude 258-vertex candidates.")),
            Describe.Lean(
                DescribeId.Create("huang-integral-norm-gap-energy"),
                DeclarationHandle.Create(Prefix + "energy"),
                H("The real energy of an integer cube vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For f : Q9 → Int, let v(x) be its real cast. Then energy f is "
                        + "v dot (3v − A v), where A is the original FALSE-prefix "
                        + "huangMatrix 9 from HypercubeSubQuorum. The definition uses "
                        + "the same actual cube vertices and matrix entries throughout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("huang-integral-norm-gap-three-le-energy"),
                DeclarationHandle.Create(Prefix + "three_le_energy"),
                H("Positive integral-vector energy is at least three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every f : Q9 → Int, the sole hypothesis 0 < energy f "
                            + "implies 3 ≤ energy f. No support, switching or graph "
                            + "regularity certificate is assumed, and attainment "
                            + "of the value three is not asserted.")),
                    Paragraph(Text(
                        "Write f = e + o using actual cube parity and form the "
                            + "integer residual r = 3e − A o. Symmetry and A² = 9I "
                            + "give sum r(x)² = 3 energy f, while A r is coordinatewise "
                            + "divisible by three. Energy is integral, so a positive "
                            + "value below three is one or two. Then r has nonempty "
                            + "support of size at most six and squared norm at most six. "
                            + "CubeSmallSupport supplies a vertex with one support "
                            + "neighbor. At that row, A r is a unit signed residual "
                            + "coordinate; divisibility by three forces its nonzero "
                            + "square to be at least nine, a contradiction."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeSmallSupport"))
        ]));
}
