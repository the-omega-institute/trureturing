using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.GateModel;

internal sealed class AlgorithmDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components GateModel Algorithm", H("Components GateModel Algorithm"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm.Coordinate"),
                H("Coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The default algorithm model's three independent native gate counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm.Token"),
                H("Token"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Gate instances retain the full one-qubit operator parameter."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm.signature"),
                H("signature"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Each default-model token has its fixed physical arity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm.coordinate"),
                H("coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Resource coordinates classify tokens without replacing their semantics."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm.operator"),
                H("operator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Fixed canonical Toffoli, CNOT and parameterized one-qubit semantics."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/GateModel/Algorithm.model"),
                H("model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The default native model used for logical algorithm resource claims."))), DescribeRole.Definition))));
}
