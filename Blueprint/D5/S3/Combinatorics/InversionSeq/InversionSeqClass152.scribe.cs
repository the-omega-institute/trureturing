using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeqClass152Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeqClass152.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two pattern-avoidance classes in Class 152 are equinumerous at every length.",
        H("Equinumerosity of Inversion Sequences in Class 152"),
        Blocks(
            Node("inversionseq-inversionseqclass152-result", "The Class 152 equinumerosity", "result",
                "For every nonnegative n, the number of inversion sequences of length n avoiding 010, 100, 102 and 210 equals the number of inversion sequences of length n avoiding 011, 201 and 210.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
