using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenCarryLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Deficit/GoldenCarryLedger",
            "The adjacency and doubling carries preserve value on both golden faces."),
        H("The Two-Face Golden Carry Ledger"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-golden-carry-rewrites-preserve-both-faces"),
                H("The golden carry rewrites preserve both faces"),
                LeanTheorem(
                    "D5/S1/Deficit/GoldenCarryLedger.carry_rewrite_face_invariant"),
                Disp(Seq(
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Quad,
                    Forall, Sp, F.Id("x"), InMacro,
                    OpenBrace, Varphi, Comma, Sp, Psi, CloseBrace, Comma, Quad,
                    Open,
                    F.Id("x"), Caret, Grp(F.Id("k"), Plus, D(1)), Plus,
                    F.Id("x"), Caret, Grp(F.Id("k"), Plus, D(2)), Eq,
                    F.Id("x"), Caret, Grp(F.Id("k"), Plus, D(3)),
                    Sp, Land, Sp,
                    D(2), F.Id("x"), Caret, Grp(F.Id("k"), Plus, D(2)), Eq,
                    F.Id("x"), Caret, Grp(F.Id("k"), Plus, D(3)), Plus,
                    F.Id("x"), Caret, F.Id("k"),
                    Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For every natural index k, the adjacency carry "
                        + "x^{k+1}+x^{k+2}=x^{k+3} and the doubling carry "
                        + "2x^{k+2}=x^{k+3}+x^k preserve value when x is either "
                        + "the expanding golden face φ=goldenRatio or the conjugate "
                        + "golden face ψ=goldenConj. Thus each internal rewrite has "
                        + "zero deficit on both faces simultaneously.")),
                    Paragraph(Text(
                        "The proof first establishes both carry identities for an arbitrary "
                        + "real root of x²=x+1. It then instantiates those parametric "
                        + "identities with the two library equations goldenRatio_sq and "
                        + "goldenConj_sq, producing the paired two-face ledger statement.")))
            )),
        []));
}
