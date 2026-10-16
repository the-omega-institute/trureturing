using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackFrameDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Register injection and disjoint frames.",
        H("Register injection and disjoint frames"),
        Blocks(
            Paragraph(Text("Every counted accepting or rejecting run lifts through an injective register map with identical primitive count. Registers outside the image retain their full words. The seven-to-nine-register instance preserves two extra frame words while running the original finite control unchanged.")),
            Describe.Lean(
                DescribeId.Create("exec-lift"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackFrame.exec_lift"),
                H("exec_lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Every counted accepting or rejecting run lifts through an injective register map with identical primitive count. Registers outside the image retain their full words. The seven-to-nine-register instance preserves two extra frame words while running the original finite control unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-extend"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackFrame.exec_extend"),
                H("exec_extend"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Every counted accepting or rejecting run lifts through an injective register map with identical primitive count. Registers outside the image retain their full words. The seven-to-nine-register instance preserves two extra frame words while running the original finite control unchanged."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackProgram"))]));
}
