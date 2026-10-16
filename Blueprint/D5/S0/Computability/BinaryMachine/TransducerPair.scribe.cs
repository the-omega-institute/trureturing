using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class TransducerPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial pairing from one common input.",
        H("Polynomial pairing from one common input"),
        Blocks(
            Paragraph(Text("The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization.")),
            Describe.Lean(
                DescribeId.Create("simulationregister-injective"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/TransducerPair.simulationRegister_injective"),
                H("simulationRegister_injective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-normalized"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/TransducerPair.exec_normalized"),
                H("exec_normalized"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-program"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/TransducerPair.exec_program"),
                H("exec_program"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polytime-pair"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/TransducerPair.polyTime_pair"),
                H("polyTime_pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The original input is saved before either transducer runs. The first result is framed, the original input is restored, and the second transducer receives that same word. The two results are assembled in their original order by PairConstructor. Actual simulations and physical output-size bounds prove a uniform polynomial tape runtime; all saved frame words survive normalization."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PairConstructor")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackFrame")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompile")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Composition"))]));
}
