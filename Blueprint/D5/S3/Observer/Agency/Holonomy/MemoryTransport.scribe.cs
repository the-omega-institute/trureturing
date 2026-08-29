using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class MemoryTransportDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Holonomy/MemoryTransport."
            + "transportWord_append";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequential memory transport along concatenated action words composes.",
        H("Memory Transport Along Action Words"),
        Blocks(Describe.Lean(
            DescribeId.Create("memory-transport-action-words"),
            DeclarationHandle.Create(Declaration),
            H("Memory Transport Along Action Words"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite action word is interpreted as left-to-right composition of memory updates.")),
                Paragraph(Text(
                    "Concatenating words therefore agrees with first transporting along the first word and then along the second."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("transport_first_append_second"), Sp, Rightarrow, Sp,
            F.Id("transport_second_after_first"), Dot));
}
