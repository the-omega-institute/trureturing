using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Tensor;

internal sealed class CertifiedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Tensor Certified", H("Core Base Tensor Certified"), Blocks(
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.unitaryOperator_prodTensor_apply"),
                H("unitaryOperator prodTensor apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("Every product-register entry is the product of the two actual subsystem entries."))), DescribeRole.Lemma))));
}
