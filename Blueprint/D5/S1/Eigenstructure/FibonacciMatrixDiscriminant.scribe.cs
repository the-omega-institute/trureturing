using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class FibonacciMatrixDiscriminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fibonacci matrix has trace one, determinant minus one, and discriminant five.",
        H("Fibonacci Matrix Discriminant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-substitution-trace-det-discriminant"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/FibonacciMatrixDiscriminant."
                    + "fibonacci_substitution_trace_det_discriminant"),
                H("Trace, determinant, and discriminant of the Fibonacci matrix"),
                StatementSource.FromAuthor(FibonacciMatrixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M be the existing Fibonacci substitution matrix [[1,1],[1,0]]. "
                        + "Its trace is 1, its determinant is -1, and its characteristic "
                        + "discriminant is 5.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle were searched before formalization. The exact "
                        + "Fibonacci instance was not present; the proof specializes "
                        + "Matrix.trace_fin_two, Matrix.det_fin_two, and Matrix.discr_fin_two.")),
                    Paragraph(Text(
                        "This declaration asserts only the three matrix equalities. It does not "
                        + "assert literal membership in SL(2,Z), which would require determinant "
                        + "one, nor the source's accompanying minimality interpretation."))),
                DescribeRole.Theorem))));

    private static Formula FibonacciMatrixFormula()
    {
        Formula matrix = F.Id("M");

        return Disp(Seq(
            Operatorname, Grp(F.Id("tr")), Open, matrix, Close, Eq, D(1), Sp, Land, Esc,
            Operatorname, Grp(F.Id("det")), Open, matrix, Close, Eq, Minus, D(1), Sp, Land, Esc,
            Operatorname, Grp(F.Id("disc")), Open, matrix, Close, Eq, D(5), Dot));
    }
}
