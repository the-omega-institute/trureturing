using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciEigenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The Fibonacci substitution has two golden eigenpairs and an exact contracting error.",
H("Fibonacci Substitution Spectrum"),
Blocks(
            Describe.Lean(
                DescribeId.Create("golden-eigenpairs-and-contracting-error"),
                DeclarationHandle.Create("D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"),
                H("Golden eigenpairs and contracting error"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc, Operatorname, Grp(F.Id("expandingEigenvector")), Neq, Sp, D(0), Sp, Land, Sp, Operatorname, Grp(F.Id("fibonacciSubstitution")), Operatorname, Grp(F.Id("expandingEigenvector")), Eq, Varphi, Operatorname, Grp(F.Id("expandingEigenvector")), Sp, Land, Sp, Operatorname, Grp(F.Id("contractingEigenvector")), Neq, Sp, D(0), Sp, Land, Sp, Operatorname, Grp(F.Id("fibonacciSubstitution")), Operatorname, Grp(F.Id("contractingEigenvector")), Eq, Operatorname, Grp(F.Id("contractingEigenvalue")), Operatorname, Grp(F.Id("contractingEigenvector")), Sp, Land, Sp, Open, F.Id("F"), Underscore, Grp(F.Id("n")), Varphi, Minus, F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Close, Eq, Minus, Operatorname, Grp(F.Id("contractingEigenvalue")), Caret, Grp(F.Id("n"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "The explicit substitution matrix has nonzero expanding and contracting eigenvectors, and the same theorem gives the exact signed Fibonacci error for every natural index."))),
                DescribeRole.Theorem)),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S0/Carrier/GoldenRatio")),
                    ]));
}
