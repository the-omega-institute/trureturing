using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decision continuations and exact word movement.",
        H("Decision continuations and exact word movement"),
        Blocks(
            Paragraph(Text("Both Boolean halts of a test dispatch to their respective continuation, counting the terminal jump. Word movement clears its destination and performs two reversals, so it preserves bit order and empties scratch. Fixed fallback words are installed by literal one-bit pushes. Disjoint finite control labels support branches with unrelated programs.")),
            Describe.Lean(
                DescribeId.Create("exec-choose"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackControl.exec_choose"),
                H("exec_choose"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Both Boolean halts of a test dispatch to their respective continuation, counting the terminal jump. Word movement clears its destination and performs two reversals, so it preserves bit order and empties scratch. Fixed fallback words are installed by literal one-bit pushes. Disjoint finite control labels support branches with unrelated programs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-moveword"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackControl.exec_moveWord"),
                H("exec_moveWord"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Both Boolean halts of a test dispatch to their respective continuation, counting the terminal jump. Word movement clears its destination and performs two reversals, so it preserves bit order and empties scratch. Fixed fallback words are installed by literal one-bit pushes. Disjoint finite control labels support branches with unrelated programs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-write"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackControl.exec_write"),
                H("exec_write"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Both Boolean halts of a test dispatch to their respective continuation, counting the terminal jump. Word movement clears its destination and performs two reversals, so it preserves bit order and empties scratch. Fixed fallback words are installed by literal one-bit pushes. Disjoint finite control labels support branches with unrelated programs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-widenleft"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackControl.exec_widenLeft"),
                H("exec_widenLeft"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Both Boolean halts of a test dispatch to their respective continuation, counting the terminal jump. Word movement clears its destination and performs two reversals, so it preserves bit order and empties scratch. Fixed fallback words are installed by literal one-bit pushes. Disjoint finite control labels support branches with unrelated programs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-widenright"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackControl.exec_widenRight"),
                H("exec_widenRight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Both Boolean halts of a test dispatch to their respective continuation, counting the terminal jump. Word movement clears its destination and performs two reversals, so it preserves bit order and empties scratch. Fixed fallback words are installed by literal one-bit pushes. Disjoint finite control labels support branches with unrelated programs."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackWords")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/TapeToStacks"))]));
}
