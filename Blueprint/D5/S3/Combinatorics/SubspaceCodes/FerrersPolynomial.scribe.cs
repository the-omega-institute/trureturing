using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class FerrersPolynomialDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial";
    private const string Digest = "The root bound for a four-term linearized polynomial gives rank at least nine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, Digest, "evidence-not-specified-by-formal-manifest"),
        H("Linearized polynomial rank"), Blocks(
            Node("evaluate-linearized", "evaluateLinearized",
                "Linearized evaluation map", DescribeRole.Definition,
                "For a finite field F of order q, an extension E of F, and coefficients a indexed by Fin 4, the F-linear map on E is the sum of the first four iterates of the q-Frobenius, scaled by the corresponding coefficients in E."),
            Node("evaluate-linearized-apply", "evaluateLinearized_apply",
                "Evaluation by Frobenius powers", DescribeRole.Theorem,
                "For a finite field F of order q and an extension field E, evaluation of a coefficient tuple a indexed by Fin 4 at x in E is the sum of aᵢ x^(qⁱ)."),
            Node("finrank-range-evaluate-linearized-ge-nine", "finrank_range_evaluateLinearized_ge_nine",
                "Rank bound in degree twelve", DescribeRole.Theorem,
                "In a finite extension of degree twelve, the evaluation map of any nonzero coefficient tuple has F-linear rank at least nine. The polynomial has distinct exponents 1, q, q² and q³ and degree at most q³. Its kernel therefore has at most q³ elements and dimension at most three."))));

    private static DocumentBlock Node(string id, string declaration, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Gid + "." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
