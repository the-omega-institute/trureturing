using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackCompileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole stack programs as polynomial tape machines.",
        H("Whole stack programs as polynomial tape machines"),
        Blocks(
            Paragraph(Text("Initialization, controller simulation and output extraction form one tape machine. A proved polynomial bound on every stack run yields a polynomial tape transducer; total runs with either decision yield a total decision machine. Determinism reflects acceptance as well as preserving it.")),
            Describe.Lean(
                DescribeId.Create("supplied-stackcompile"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackCompile.polyTime_of_stack"),
                H("polyTime_of_stack"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text(
                    "This declaration and its proof are attributed immutable source supply. "
                    + "The mathematical namespace and proof body are preserved. Full license, "
                    + "source correspondence and the finite retirement contract are recorded "
                    + "in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies "
                    + "no new classification or independent mathematical escape content."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackSimulation")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackInit")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PolynomialBound"))]));
}
