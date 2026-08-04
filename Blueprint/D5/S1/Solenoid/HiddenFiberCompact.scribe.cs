using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class HiddenFiberCompactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Solenoid/HiddenFiberCompact",
                "The hidden fiber is closed, compact, and sequentially compact coordinatewise."),
            H("Hidden Fiber Compactness"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("hidden-fiber-closed-compact-sequentially-compact"),
                    H("The hidden fiber is compact in every equivalent sense"),
                    LeanTheorem(
                        "D5/S1/Solenoid/HiddenFiberCompact."
                        + "hiddenFiber_closed_compact_seqCompact"),
                    Disp(Seq(Sigma, Eq, Left, OpenBrace, Theta, Colon, Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), To, Mathbb, Grp(F.Id("R")), Slash, Mathbb, Grp(F.Id("Z")), Esc, Middle, Bar, Esc, Forall, Sp, F.Id("m"), Comma, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc, F.Id("n"), Theta, Underscore, Grp(F.Id("mn")), Eq, Theta, Underscore, F.Id("m"), Right, CloseBrace, Comma, Quad, Sp, Pi, Open, Theta, Close, Eq, Theta, Underscore, D(1), Comma, Quad, Sp, F.Id("K"), Underscore, Grp(Infty), Eq, Ker, Pi, Eq, OpenBrace, Theta, InMacro, Sigma, Mid, Theta, Underscore, D(1), Eq, D(0), CloseBrace, Colon, Quad, Sp, F.Id("K"), Underscore, Grp(Infty), Esc, F.Text, Grp(F.Id("is"), Sp, F.Id("closed")), Esc, Land, Esc, F.Id("K"), Underscore, Grp(Infty), Esc, F.Text, Grp(F.Id("is"), Sp, F.Id("compact")), Esc, Land, Esc, Forall, Sp, Open, F.Id("x"), Underscore, F.Id("j"), Close, Underscore, Grp(F.Id("j"), InMacro, Mathbb, Grp(F.Id("N"))), Subseteq, Sp, F.Id("K"), Underscore, Grp(Infty), Comma, Esc, Exists, Sp, F.Id("x"), InMacro, Sp, F.Id("K"), Underscore, Grp(Infty), Comma, Esc, Exists, Sp, Phi, Colon, Mathbb, Grp(F.Id("N")), To, Mathbb, Grp(F.Id("N")), Comma, Esc, Phi, Esc, F.Text, Grp(F.Id("strictly"), Sp, F.Id("increasing")), Esc, Land, Esc, Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc, F.Id("x"), Underscore, Grp(Phi, Open, F.Id("j"), Close, Comma, F.Id("m")), Longrightarrow, Sp, F.Id("x"), Underscore, F.Id("m"), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Continuity of the visible projection makes its zero fiber closed. "
                        + "The ambient solenoid is compact, so the fiber is compact. Its "
                        + "countable product topology is first countable, hence compactness "
                        + "gives a convergent subsequence; the formal coordinatewise "
                        + "convergence equivalence identifies this with the diagonal, "
                        + "layer-by-layer limit.")))))));
}
