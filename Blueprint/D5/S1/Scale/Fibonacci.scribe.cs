using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powers of the golden generator have consecutive Fibonacci coordinates.",
        H("Golden Powers and Fibonacci Coordinates"),
        Blocks(
            Paragraph(Text(
                "Write a golden integer as a pair (a,b), representing a+b phi, where phi squared equals phi plus one. The Fibonacci sequence starts with F_0=0 and F_1=1.")),
            Describe.Lean(
                DescribeId.Create("golden-power-fibonacci-coordinates"),
                DeclarationHandle.Create("D5/S1/Scale/Fibonacci.golden_phi_pow_eq_fib_pair"),
                H("Coordinates of positive powers"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    Varphi, Caret, Grp(F.Id("n"), Plus, D(1)), Eq,
                    Open, F.Id("F"), Underscore, F.Id("n"), Comma,
                    F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Close))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "For every natural n, the two integral coordinates of phi^(n+1) are F_n and F_(n+1). Multiplication by phi sends (a,b) to (b,a+b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-cassini-golden-norm"),
                DeclarationHandle.Create("D5/S1/Scale/Fibonacci.fib_cassini_from_golden_norm"),
                H("Cassini identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma,
                    F.Id("F"), Underscore, F.Id("n"),
                    F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(2)), Minus,
                    F.Id("F"), Underscore, Grp(F.Id("n"), Plus, D(1)), Caret, D(2), Eq,
                    Open, Minus, D(1), Close, Caret, Grp(F.Id("n"), Plus, D(1))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "Taking the integer norm of the coordinate identity gives Cassini's identity. The norm of phi is minus one."))),
                DescribeRole.Theorem))));
}
