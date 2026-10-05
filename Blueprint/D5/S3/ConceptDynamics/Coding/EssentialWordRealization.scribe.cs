using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class EssentialWordRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/EssentialWordRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Essential finite directed multigraphs extend every positive legal named-edge word to one actual bi-infinite history.",
        H("Prescribed-word realization"),
        Blocks(
            Describe.Lean(DescribeId.Create("realized-word-is-legal"),
                DeclarationHandle.Create(Prefix + "realized_legal"),
                H("The constructed history has both seams"),
                StatementSource.FromAuthor(Disp(Call("LegalHistory", F.Id("realized")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Backward tails use an actual incoming edge at every vertex and forward tails use an actual outgoing edge. The supplied finite word is kept unchanged in the middle, so the negative seam, every interior seam, and the positive seam are all legal."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("every-word-has-history"),
                DeclarationHandle.Create(Prefix + "every_prescribed_word_has_actual_history"),
                H("Every prescribed word occurs in an actual history"),
                StatementSource.FromAuthor(Disp(Call("ExistsHistoryContaining", F.Id("word")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The witness is an Int-indexed sequence of the original edge type. It contains every named edge of the input word at its original position; no language extension or strong-connectivity hypothesis is used."))),
                DescribeRole.Theorem))));
}
