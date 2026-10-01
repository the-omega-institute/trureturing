using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152RightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Right.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance of 011, 201 and 210 separates at the last zero of an inversion sequence.",
        H("Structure of the Right Avoidance Class"),
        Blocks(
            Node("inversionseq-inversionseq152right-avoid011-iff-positive-distinct", "Distinct positive entries", "avoid011_iff_positive_distinct",
                "An inversion sequence avoids 011 if and only if its positive entries are pairwise distinct.", DescribeRole.Theorem),
            Node("inversionseq-inversionseq152right-right-last-zero-structure", "Characterization at the last zero", "right_last_zero_structure",
                "Suppose an inversion sequence has its last zero at position z. It avoids 011, 201 and 210 if and only if its positive entries are pairwise distinct, its positive entries through position z are strictly increasing in order of occurrence, every entry through position z is less than every later entry, and no three increasing positions after z have their first entry larger than both their second and third entries.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
