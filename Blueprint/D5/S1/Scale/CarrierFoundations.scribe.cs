using static StrataLint.Scribe.DefinitionDsl;

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
                new DocumentBlock.Describe(
                    DescribeId.Create("golden-carrier-foundations"),
                    DescribeKind.Theorem,
                    H("Conjugation, norm, units, and factorization of the golden carrier"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/CarrierFoundations.golden_carrier_foundations")),
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
                            + "declaration without re-proving any of them."))),
                    LatexStatement.Create(
                        @"$$\exists\,\sigma\in\operatorname{Aut}(\mathcal{O}_\varphi):\ "
                        + @"\sigma=\overline{(\,\cdot\,)},\ \sigma^{2}=\mathrm{id};\quad "
                        + @"N(xy)=N(x)\,N(y);\quad "
                        + @"\mathcal{O}_\varphi^{\times}=\{\pm\varphi^{n}\mid n\in\mathbb{Z}\},\ "
                        + @"N(\varphi)=-1;\quad "
                        + @"\mathcal{O}_\varphi\ \text{is a PID and a UFD.}$$")))));
}
