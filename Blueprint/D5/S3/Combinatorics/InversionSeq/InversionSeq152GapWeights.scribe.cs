using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152GapWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152GapWeights.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weights on successive increases separate the last positive increase from all earlier increases.",
        H("Separation of Internal and Final Gap Weights"),
        Blocks(
            Node("inversionseq-inversionseq152gapweights-gap-weight-isolation", "Isolating the final increase", "gap_weight_isolation",
                "Let I and T be nonnegative integer-valued functions with I(0) = T(0) = 0. For a weakly increasing word whose entries are at least a given preceding value p, form the successive differences after adjoining p and discard the zero differences. Weight each original difference by T when its destination is the maximum entry and by I otherwise, using p as the maximum for the empty word. The total equals the sum of I over all positive differences except the last, plus T of the last positive difference, with zero used when there is none.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
