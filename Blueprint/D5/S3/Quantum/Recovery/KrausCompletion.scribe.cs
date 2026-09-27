using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class KrausCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit row-reset Kraus operators complete the input effect and produce the repository canonical CPTP channel. Spectral inverse construction is a separate obligation.",
        H("KrausCompletion"),
        Blocks(new[]
        {
                "row_reset_action",
                "complete_kraus_action",
                "complete_quantum_channel"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/KrausCompletion." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/knilllaflamme1997correction")),
            Blocks(Paragraph(Text("Explicit row-reset Kraus operators complete the input effect and produce the repository canonical CPTP channel. Spectral inverse construction is a separate obligation."))),
            DescribeRole.Theorem)).ToArray())));
}
