using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Components.Gates.ControlledPhase;

internal sealed class SemanticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Components Gates ControlledPhase Semantics", H("Components Gates ControlledPhase Semantics"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phaseWeight"),
                H("phaseWeight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private def phaseWeight (angle : Real) (bit : Fin 2) : Complex."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.cnot_twice"),
                H("cnot twice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma cnot_twice (basis : layout.Basis) : AlgorithmGate.cnotPermutation (AlgorithmGate.cnotPermutation basis) = basis."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.conjugate_diagonal"),
                H("conjugate diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma conjugate_diagonal (register : Register) (permutation : Equiv.Perm register.Index) (involution : Function.Involutive permutation) (weight : register.Index → Complex) : ((UnitaryOperator.ofPerm (R."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.target_diagonal"),
                H("target diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma target_diagonal (angle : Real) : (operator angle : HilbertOperator layout.register) = Matrix.diagonal (fun basis => qftControlledPhaseFactor (n."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.phase_product"),
                H("phase product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma phase_product (angle : Real) (basis : layout.Basis) : phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation basis) (1 : Fin 2)) * (phaseWeight (angle / 2) (basis (1 : Fin 2)) * phaseWeight (angle / 2) (basis (0 : Fin 2))) = qftControlledPhaseFactor (n."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.word_diagonal"),
                H("word diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("private lemma word_diagonal (oracles : OracleModel) (angle : Real) (environment : oracles.Interpretation) : (((circuit oracles angle).matrix environment) : HilbertOperator layout.register) = Matrix.diagonal (fun basis => phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation basis) (1 : Fin 2)) * (phaseWeight (angle / 2) (basis (1 : Fin 2)) * phaseWeight (angle / 2) (basis (0 : Fin 2))))."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Components/Gates/ControlledPhase/Semantics.controlledPhase_circuit_matrix"),
                H("controlledPhase circuit matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("The complete five-gate native word realizes the original target with exact phase."))), DescribeRole.Lemma))));
}
