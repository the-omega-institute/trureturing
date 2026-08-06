using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class CarrierFoundationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Scale/CarrierFoundations",
                "Frozen proofs assemble conjugation, norm, units, and unique factorization."),
            H("Golden Carrier Foundations"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("golden-carrier-foundations"),
                    H("Conjugation, norm, units, and factorization of the golden carrier"),
                    LeanTheorem(
                        "D5/S1/Scale/CarrierFoundations.golden_carrier_foundations"),
                    Disp(Seq(Exists, Thin, SigmaLower, InMacro, Operatorname, Grp(F.Id("Aut")), Open, Mathcal, Grp(F.Id("O")), Underscore, Varphi, Close, Colon, Esc, SigmaLower, Eq, Overline, Grp(Open, Thin, Cdot, Thin, Close), Comma, Esc, SigmaLower, Caret, Grp(D(2)), Eq, Mathrm, Grp(F.Id("id")), Semi, Quad, Sp, F.Id("N"), Open, F.Id("xy"), Close, Eq, F.Id("N"), Open, F.Id("x"), Close, Thin, F.Id("N"), Open, F.Id("y"), Close, Semi, Quad, Sp, Mathcal, Grp(F.Id("O")), Underscore, Varphi, Caret, Grp(Times), Eq, OpenBrace, Pm, Varphi, Caret, Grp(F.Id("n")), Mid, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z")), CloseBrace, Comma, Esc, F.Id("N"), Open, Varphi, Close, Eq, Minus, D(1), Semi, Quad, Sp, Mathcal, Grp(F.Id("O")), Underscore, Varphi, Esc, F.Text, Grp(F.Id("is"), Sp, F.Id("a"), Sp, F.Id("PID"), Sp, F.Id("and"), Sp, F.Id("a"), Sp, F.Id("UFD"), Dot))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The golden integer carrier admits a ring automorphism that agrees "
                            + "pointwise with conjugation and is involutive. The integer norm is "
                            + "multiplicative. An element is a unit exactly when it is a signed "
                            + "integral power of the golden ratio, whose norm is minus one. The "
                            + "carrier is a principal ideal ring and a unique factorization "
                            + "monoid.")),
                        Paragraph(Text(
                            "The statement is assembly-only: each clause is witnessed by its "
                            + "frozen proof — the conjugation equivalence, norm "
                            + "multiplicativity, the signed-power unit classification, and the "
                            + "principal-ideal and unique-factorization instances — so the "
                            + "theorem packages the four foundations behind a single "
                            + "declaration without re-proving any of them.")))
                )),
            [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Norm"))]));
}
