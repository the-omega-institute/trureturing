using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152ReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection exchanges ascent lengths and descent lengths while reversing their order.",
        H("Run Lengths under Dyck Path Reflection"),
        Blocks(
            Node("inversionseq-inversionseq152reflection-reflection-runs", "Reflected ascent lengths", "reflection_runs",
                "Reflect a Dyck path by reversing its step word and exchanging up steps with down steps. The list of lengths of its nonempty ascents is the reverse of the list of lengths of the original path's nonempty descents.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
