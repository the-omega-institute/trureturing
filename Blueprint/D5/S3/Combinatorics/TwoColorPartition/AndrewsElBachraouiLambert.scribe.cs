using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiLambertDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiLambert.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd divisors encode the shifted Lambert coefficients.",
        H("The Shifted Lambert Coefficient"),
        Blocks(
            Node("andrews-el-bachraoui-lambert-lambert-divisor-coefficient", "Lambert coefficient and divisor count", "lambert_divisor_coefficient", "For every natural number n, the coefficient of degree n in the finite shifted Lambert sum, increased by two, equals the number of positive divisors of 2n plus 5. The correspondence sends a summand indexed by j to the odd divisor 2j plus 3 and removes the two endpoint divisors.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
