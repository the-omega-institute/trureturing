using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class CompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executed polynomial transducer composition.",
        H("Executed polynomial transducer composition"),
        Blocks(
            Paragraph(Text("The first tape transducer is simulated and normalized to its exact output word before the second runs. Physical output size bounds the second input. Actual counted stack and tape simulations establish composition for total true-halting transducers.")),
            Describe.Lean(
                DescribeId.Create("supplied-composition"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/Composition.comp"),
                H("PolyTime.comp"),
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
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TapeToStacks")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PolynomialBound")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompile"))]));
}
