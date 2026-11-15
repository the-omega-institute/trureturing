using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Tensor;

internal sealed class CertifiedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Tensor Certified", H("Core Base Tensor Certified"), Blocks(
            Describe.Lean(DescribeId.Create("certified-tensor"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor"),
                H("Certified tensor operator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For arbitrary finite registers R and S and unitary operators U and V, UnitaryOperator.prodTensor U V is their Kronecker product reindexed by Register.prodIndexEquiv R S. Its unitary certificate uses the two input unitary certificates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tensor-entry-helper"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.prodTensor_apply"),
                H("Tensor entry helper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every finite R and S, U : UnitaryOperator R, V : UnitaryOperator S and i,j : (Register.prod R S).Index, prodTensor U V i j = U i.1 j.1 * V i.2 j.2. The public entry lemma below consumes this helper."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Tensor/Certified.unitaryOperator_prodTensor_apply"),
                H("unitaryOperator prodTensor apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Every product-register entry is the product of the two actual subsystem entries."))), DescribeRole.Lemma))));
}
