using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeqDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeqDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inversion sequences and pattern avoidance define the equinumerosity assertions for Classes 152 and 207.",
        H("Inversion Sequences and Pattern Avoidance"),
        Blocks(
            Node("inversionseq-inversionseqdefs-is-inversion-seq", "Inversion sequences", "IsInversionSeq",
                "A word of nonnegative integers is an inversion sequence when its entry at each position i, numbered from zero, is at most i. The empty word is included.", DescribeRole.Definition),
            Node("inversionseq-inversionseqdefs-avoiders", "Avoiders of a fixed length", "avoiders",
                "For a nonnegative integer n and a list B of patterns, the set I_n(B) consists of inversion sequences of length n avoiding every pattern in B. A pattern occurrence preserves both equality and relative order of entries.", DescribeRole.Definition),
            Node("inversionseq-inversionseqdefs-claim152", "The Class 152 assertion", "claim152",
                "The Class 152 assertion is the proposition that, for every nonnegative n, the number of inversion sequences of length n avoiding 010, 100, 102 and 210 equals the number avoiding 011, 201 and 210.", DescribeRole.Definition),
            Node("inversionseq-inversionseqdefs-claim207", "The Class 207 assertion", "claim207",
                "The Class 207 assertion is the proposition that, for every nonnegative n, the number of inversion sequences of length n avoiding 100, 101, 110 and 201 equals the number avoiding 101, 110, 120 and 210.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
