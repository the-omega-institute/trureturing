using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class OriginalClauseGuardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite lexical repair transducer.",
        H("A finite lexical repair transducer"),
        Blocks(
            Paragraph(Text("The finite control is the original eleven-state unrestricted lexical phase. Each raw input bit causes one literal stack pop, followed by an empty pop and a halt. A saved copy restores every accepted word without changing any payload bit. A rejected phase installs the fixed fallback word by actual primitive pushes. The validity bit in this module is the ending phase of Unrestricted.scanPhase; relating it to the exact mathematical decoder is a separate source-semantic obligation. The supplied FinTM2 parser is not used as an execution certificate for this tape model.")),
            Describe.Lean(
                DescribeId.Create("exec-scan"),
                DeclarationHandle.Create("D5/S0/Computability/OriginalClauseGuard.exec_scan"),
                H("exec_scan"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The finite control is the original eleven-state unrestricted lexical phase. Each raw input bit causes one literal stack pop, followed by an empty pop and a halt. A saved copy restores every accepted word without changing any payload bit. A rejected phase installs the fixed fallback word by actual primitive pushes. The validity bit in this module is the ending phase of Unrestricted.scanPhase; relating it to the exact mathematical decoder is a separate source-semantic obligation. The supplied FinTM2 parser is not used as an execution certificate for this tape model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polytime-repair"),
                DeclarationHandle.Create("D5/S0/Computability/OriginalClauseGuard.polyTime_repair"),
                H("polyTime_repair"),
                StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("The finite control is the original eleven-state unrestricted lexical phase. Each raw input bit causes one literal stack pop, followed by an empty pop and a halt. A saved copy restores every accepted word without changing any payload bit. A rejected phase installs the fixed fallback word by actual primitive pushes. The validity bit in this module is the ending phase of Unrestricted.scanPhase; relating it to the exact mathematical decoder is a separate source-semantic obligation. The supplied FinTM2 parser is not used as an execution certificate for this tape model."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/OriginalClauseLanguages")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackControl")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackCompile")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackPair"))]));

    private static Formula All(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, p);

    private static Formula Presentation0() =>
        All("fallback", Id("Word"), Call("PolyTime", Call("repair", Id("fallback"))));
}
