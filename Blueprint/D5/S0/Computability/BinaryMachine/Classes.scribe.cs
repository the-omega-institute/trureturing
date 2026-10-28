using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class ClassesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complexity classes in one concrete machine model.",
        H("Complexity classes in one concrete machine model"),
        Blocks(
            Paragraph(Text("PolyTime requires one actual total tape transducer that halts true and writes the specified output on every raw binary word. NP uses a total polynomial-time decision machine on the exact pairWords instance and witness bytes, with a uniform polynomial witness bound. PolyRed is a total deterministic polynomial many-one reduction.")),
            Describe.Lean(
                DescribeId.Create("supplied-classes"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/Classes.NPComplete"),
                H("NPComplete"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text(
                    "This declaration and its proof are attributed immutable source supply. "
                    + "The mathematical namespace and proof body are preserved. Full license, "
                    + "source correspondence and the finite retirement contract are recorded "
                    + "in docs/reports/licenses/RBarishBinaryMachine.md. This port supplies "
                    + "no new classification or independent mathematical escape content."))),
                DescribeRole.Definition)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/Machine"))]));
}
