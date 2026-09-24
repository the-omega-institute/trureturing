using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class KrausLeftInverseNecessityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite Kraus left inversion forces scalar error products. Scalarity of composite Kraus maps is derived from a positive commutator defect. The represented-family quantifier is explicit.",
        H("KrausLeftInverseNecessity"),
        Blocks(new[]
        {
            "identity_kraus_commute",
            "identity_kraus_scalar",
            "left_inverse_error_products"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/KrausLeftInverseNecessity." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/knilllaflamme1997correction"), LibraryNoteRef.Create("D5/L/choijohnstonkribs2009multiplicative")),
            Blocks(Paragraph(Text("Actual finite Kraus left inversion forces scalar error products. Scalarity of composite Kraus maps is derived from a positive commutator defect. The represented-family quantifier is explicit."))),
            DescribeRole.Theorem)).ToArray())));
}
