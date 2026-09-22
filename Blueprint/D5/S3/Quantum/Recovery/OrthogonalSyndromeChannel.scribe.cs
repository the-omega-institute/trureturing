using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class OrthogonalSyndromeChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete canonical CPTP encoding and full-space decoding of arbitrary positive unit-trace syndrome densities, together with the multiplicative logical algebra. This is classical orthogonal-syndrome correction, with no novelty claim.",
        H("OrthogonalSyndromeChannel"),
        Blocks(new[]
        {
                "logical_representation_mul",
                "logical_representation_star",
                "logical_representation_on_copy",
                "logical_representation_restrict",
                "logical_representation_injective",
                "logical_action_on_encoding",
                "code_support_projection",
                "code_support_on_copy",
                "code_support_on_encoding",
                "full_syndrome_decoder",
                "encoding_kraus_gram",
                "encoding_kraus_action",
                "gram_syndrome_encoder",
                "positive_syndrome_encoder",
                "reversible_syndrome_channels"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel." + name),
            H(name.Replace('_', ' ')),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/knilllaflamme1997correction"),
                LibraryNoteRef.Create("D5/L/benykempfkribs2007observables")),
            Blocks(Paragraph(Text("Concrete canonical CPTP encoding and full-space decoding of arbitrary positive unit-trace syndrome densities, together with the multiplicative logical algebra. This is classical orthogonal-syndrome correction, with no novelty claim."))),
            DescribeRole.Theorem)).ToArray())));
}
