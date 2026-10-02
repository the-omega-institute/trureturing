using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DottedStack;

internal sealed class ShiehYangYuTwelveDotDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDot.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 12-dot machine sorts a central binomial number of permutations of each positive size.",
        H("The Central Binomial Count for the 12-Dot Machine"),
        Blocks(
            Node("syy-twelve-dot-result-theorem", "Count the machine-sortable permutations", "result", "For every natural number n at least one, exactly the binomial coefficient choosing n minus one from 2n minus two permutations of [1,...,n] are sent to [1,...,n] by peak-run reversal followed by West's stack map. Peak-run reversal is the closed form in Proposition 3.1 of the cited paper, so this count is the assertion of Conjecture 6.1. West's criterion reduces sortability to 231 avoidance after peak-run reversal. The fibres give two choices per record of an avoiding permutation of size n minus one. The permutation-to-Dyck-path bijection carries the number of records to the number of primitive excursions. Coloring and reflecting these excursions gives all balanced bridges with n minus one up steps and n minus one down steps, counted by their up-step positions.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
