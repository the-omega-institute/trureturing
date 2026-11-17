using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SupportedEigenSaturationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supported Huang eigenvector saturates each selected edge; its nonzero "
            + "coordinates have full induced degree and admit a switching function.",
        H("Saturation of supported Huang eigenvectors"),
        Blocks(
            Paragraph(Text(
                "Let n and d be arbitrary natural numbers, U a finite subset of Q n, "
                    + "and z : Q n → Real. The hypotheses bound every degree of the "
                    + "actual induced graph on U by d, require z to vanish outside U, "
                    + "and give the ambient equation A z = d z. The zero vector and "
                    + "empty U are allowed. A is the original huangMatrix from "
                    + "HypercubeSubQuorum, reused through BalancedCriticalSpectrum: "
                    + "TRUE selects the first recursive block, so its directional "
                    + "signs use earlier FALSE coordinates.")),
            Paragraph(Text(
                "The proof sums the nonnegative squared residuals "
                    + "(z(x) − A(x,y) z(y))² over actual edges with both endpoints "
                    + "in U. The existing matrix_support identifies the unit edge "
                    + "coefficients and zero nonedge coefficients. The support "
                    + "hypothesis restricts the ambient equation to selected rows; "
                    + "expansion and exchange of the finite sums express the energy "
                    + "as twice the degree-weighted squared norm minus twice d times "
                    + "the squared norm. The actual degree bound makes this at most "
                    + "zero, so each edge residual vanishes.")),
            Describe.Lean(
                DescribeId.Create("supported-eigen-nonzero-support"),
                DeclarationHandle.Create(Prefix + "nonzeroSupport"),
                H("The actual nonzero selected coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "nonzeroSupport U z is U filtered by z(x) ≠ 0. Its membership "
                        + "lemma provides both selection and nonvanishing. This set "
                        + "may be empty and may meet several connected components; "
                        + "nonzeroSupport_isBalanced supplies its switching function."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supported-eigen-edge-identity"),
                DeclarationHandle.Create(Prefix + "edge_identity"),
                H("Every selected edge attains exact signed equality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the degree, support and ambient eigen-equation hypotheses, "
                        + "x and y in U joined by an actual cube edge satisfy "
                        + "z(x) = A(x,y) z(y). This is the pointwise consequence of "
                        + "the vanishing squared energy. The live zero_of_adj_zero "
                        + "helper propagates a zero across such an edge, with both "
                        + "endpoints required to belong to U. The degree and balance "
                        + "results below consume the same signed equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-eigen-full-degree"),
                DeclarationHandle.Create(Prefix + "degree_eq_of_ne_zero"),
                H("A nonzero selected coordinate has degree d"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With the same three hypotheses, x in U and z(x) ≠ 0 imply "
                        + "that x has degree exactly d in the actual induced graph "
                        + "on U. Substituting edge_identity into the selected row "
                        + "turns that row into degree(x) times z(x); cancellation of "
                        + "the nonzero coordinate gives the claimed natural degree. "
                        + "There is no relation assumed between n and d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-eigen-balanced-support"),
                DeclarationHandle.Create(Prefix + "nonzeroSupport_isBalanced"),
                H("The nonzero support is switching-balanced"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The degree bound, vanishing outside U and ambient eigen-equation "
                        + "give BalancedCriticalSpectrum.IsBalanced (nonzeroSupport U z). "
                        + "The witness is 1 where z(x) is positive and −1 otherwise. "
                        + "On the nonzero support, edge_identity and the original "
                        + "unit Huang coefficients show that each edge coefficient "
                        + "equals the product of the endpoint signs. Connectedness "
                        + "and nonemptiness are not hypotheses."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum"))
        ]));
}
