using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class FiniteKrausReversibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar error products construct a normalized finite Kraus left inverse. Spectral zero weights are eliminated explicitly. The reverse implication and canonical channel interface are treated in neighboring modules.",
        H("FiniteKrausReversibility"),
        Blocks(new[]
        {
            "scalar_products_construct_left_inverse"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/FiniteKrausReversibility." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible")),
            Blocks(Paragraph(Text("Scalar error products construct a normalized finite Kraus left inverse. Spectral zero weights are eliminated explicitly. The reverse implication and canonical channel interface are treated in neighboring modules."))),
            DescribeRole.Theorem)).ToArray())));
}
