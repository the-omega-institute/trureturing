using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.IndecomposableInversion;

internal sealed class FranklinInversionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/franklin2024inversions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number of indecomposable 321- and 1342-avoiders with k inversions is k(k - 1)/2 + 1, refuting the conjectured count k(k + 1)/2 + 1.",
        H("FranklinInversion"),
        Blocks(
            Node("franklininversion-avoiders-ncard-theorem", "The corrected count", "avoiders_ncard", "For every nonnegative integer k, the number of indecomposable permutations with exactly k inversions avoiding 321 and 1342 is k(k - 1)/2 + 1. At k equal to zero the count is one; subtraction of natural numbers is truncated at zero.", DescribeRole.Theorem),
            Node("franklininversion-result-theorem", "Refutation of the conjectured count", "result", "The conjecture that I_k(321, 1342) has k(k + 1)/2 + 1 elements for every nonnegative integer k is false. At k equal to one, the corrected count is one, whereas the conjectured formula gives two.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
