using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.BinaryMachine;

internal sealed class StackPowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executed unary polynomial budgets.",
        H("Executed unary polynomial budgets"),
        Blocks(
            Paragraph(Text("Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included.")),
            Describe.Lean(
                DescribeId.Create("exec-multiply"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackPower.exec_multiply"),
                H("exec_multiply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exec-power"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackPower.exec_power"),
                H("exec_power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomialbound-time"),
                DeclarationHandle.Create("D5/S0/Computability/BinaryMachine/StackPower.polynomialBound_time"),
                H("polynomialBound_time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("Register two holds the unary base and register three holds the accumulator. Multiplication repeats a copy-and-transfer of the preserved base once for each accumulator bit. A fixed finite sequence of these multiplications computes c times n to the e, starting from literal c. All work stacks are restored, the two input frame registers are preserved, and the full exact instruction recurrence has a polynomial envelope. Zero coefficients, zero exponents and empty unary bases are included."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackControl")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PolynomialBound"))]));
}
