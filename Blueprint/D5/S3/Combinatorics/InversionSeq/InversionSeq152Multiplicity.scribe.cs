using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152MultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Multiplicity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted labelled binary choices separate into label multiplicities and one binary word for each label.",
        H("Multiplicities of Ordered Binary Choices"),
        Blocks(
            Node("inversionseq-inversionseq152multiplicity-ordered-choice-multiplicity-bijection", "Multiplicity decomposition and enumeration", "ordered_choice_multiplicity_bijection",
                "Let A be a finite linearly ordered set with a specified set of permitted labels, and fix a nonnegative length n. Words of n label-bit pairs with weakly increasing labels and false bits at all nonpermitted labels are in bijection with multiplicities on A summing to n together with, for each label, a binary word of its multiplicity, constrained to be all false for nonpermitted labels. Each binary word is exactly the subsequence of bits at its label in the original word. For fixed multiplicities, the number of such families is the product over labels of 2 to the power of the multiplicity for permitted labels and 1 to that power for other labels.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
