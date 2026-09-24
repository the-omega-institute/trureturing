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
                "logical_representation_on_copy",
                "full_syndrome_decoder",
                "encoding_kraus_gram",
                "encoding_kraus_action",
                "positive_syndrome_encoder"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/knilllaflamme1997correction"),
                LibraryNoteRef.Create("D5/L/benykempfkribs2007observables")),
            Blocks(Paragraph(Text("Concrete canonical CPTP encoding and full-space decoding of arbitrary positive unit-trace syndrome densities, together with the multiplicative logical algebra. This is classical orthogonal-syndrome correction, with no novelty claim."))),
            DescribeRole.Theorem)).ToArray())));
}
