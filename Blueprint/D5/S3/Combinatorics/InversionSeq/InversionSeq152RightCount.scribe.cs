using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152RightCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152RightCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generating function for 011, 201 and 210 avoiders is expressed in terms of the Catalan series.",
        H("Enumeration of the Right Avoidance Class"),
        Blocks(
            Node("inversionseq-inversionseq152rightcount-right-avoider-enumeration", "The right avoidance generating function", "right_avoider_enumeration",
                "Over the rational numbers, let A(x) have constant coefficient one and, in each positive degree n, the number of inversion sequences of length n avoiding 011, 201 and 210. Write C(x) for the Catalan series and t(x) = x C(x). Then 2 (1 - x) (1 - 2 t(x)) (A(x) - 1) = x (2 - 2 t(x)).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
