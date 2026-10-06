using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelUnboundedGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of every integral q-metallic solution admit a uniform exponential bound in their degree.",
        H("Exponential Growth Bound for Metallic Coefficients"),
        Blocks(
            Node("metallic-hankel-unbounded-growth-coefficient-growth", "An exponential coefficient majorant", "coefficient_growth",
                "For every positive integer n, every integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, and every nonnegative integer m, the absolute value of [q^m]Phi is at most (4(n+5))^m. Here [n]_q = 1+q+...+q^{n-1}. The estimate includes m equal to zero and the golden case n equal to one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
