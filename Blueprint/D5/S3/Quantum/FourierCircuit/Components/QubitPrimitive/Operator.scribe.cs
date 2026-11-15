using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.QubitPrimitive;

internal sealed class OperatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components QubitPrimitive Operator", H("Components QubitPrimitive Operator"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.QubitPrimitive"),
                H("QubitPrimitive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Wire-addressed declarations for the common reversible qubit primitives."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.applyLabel"),
                H("applyLabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Classical computational-basis action of one primitive declaration."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm"),
                H("perm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Certified basis permutation of one primitive declaration."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.perm_apply"),
                H("perm apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("lemma perm_apply {n : Nat} (primitive : QubitPrimitive n) (label : Fin (2 ^ n)) : primitive.perm label = primitive.applyLabel label."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator"),
                H("operator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Canonical unitary operator of one addressed primitive declaration."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/QubitPrimitive/Operator.operator_apply_ket"),
                H("operator apply ket"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma operator_apply_ket {n : Nat} (primitive : QubitPrimitive n) (label : Fin (2 ^ n)) : primitive.operator.apply (NormalizedVector.ket label) = NormalizedVector.ket (primitive.applyLabel label)."))), DescribeRole.Lemma))));
}
