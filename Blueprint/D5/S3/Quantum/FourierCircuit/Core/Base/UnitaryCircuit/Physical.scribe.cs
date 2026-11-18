using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit;

internal sealed class PhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base UnitaryCircuit Physical", H("Core Base UnitaryCircuit Physical"), Blocks(
            Paragraph(Text("For every injective physical map from Nat to Nat, the relabel constructions for QuantumLayout.Embedding, GateModel.Application, OracleModel.Application, UnitaryLeaf, UnitarySequence and UnitaryCircuit use that same map. Embeddings keep their logical position maps. Applications keep the actual native token or oracle query. The sequence recursion preserves identity, leaf, sequential, embedded and disjoint parallel constructors, and the circuit construction wraps that relocated sequence. The matrix and event-trace lemmas below compare those literal constructions.")),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.liftOperator_relabel"),
                H("liftOperator relabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The same local operator acts on the same coordinate values after physical relocation."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.toUnitary_relabel"),
                H("toUnitary relabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Logical operators are unchanged because relocation preserves every coordinate value."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration7"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.eventTrace_relabel"),
                H("eventTrace relabel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Relocation retains each original native and query occurrence in execution order."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration9"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix_internal"),
                H("relabel matrix internal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma relabel_matrix_internal (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (environment : oracles.Interpretation) : ((circuit.relabel physical).matrix environment) = (circuit.matrix environment)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration10"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_matrix"),
                H("relabel matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma relabel_matrix (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (environment : oracles.Interpretation) : ((circuit.relabel physical).matrix environment) = (circuit.matrix environment)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration11"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace_internal"),
                H("relabel eventTrace internal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma relabel_eventTrace_internal (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (operations : ClassicalOpModel."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration12"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/UnitaryCircuit/Physical.relabel_eventTrace"),
                H("relabel eventTrace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("public lemma relabel_eventTrace (circuit : UnitaryCircuit gates oracles layout) (physical : Nat ↪ Nat) (operations : ClassicalOpModel."))), DescribeRole.Lemma))));
}
