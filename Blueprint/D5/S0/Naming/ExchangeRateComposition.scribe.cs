using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class ExchangeRateCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exchange rates multiply when normal translations compose.",
        H("Exchange Rate Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exchange-rates-multiply-under-normal-composition"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/ExchangeRateComposition.exchange_rate_composition"),
                H("Exchange rates multiply under normal composition"),
                StatementSource.FromAuthor(Equal(
                    Call("limitAlong", Id("lA"),
                        Call("ratio",
                            Call("h0", Id("a")),
                            Call("h2", Call("tau2", Call("tau1", Id("a")))))),
                    Multiply(Id("rho1"), Id("rho2")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source and intermediate filters represent the declared high-resource "
                        + "domains of the two translations, and a target filter records the target "
                        + "domain. Normality sends the first filter to the intermediate filter and the "
                        + "intermediate filter to the target filter; total maps encode the source domain "
                        + "and composite-domain conditions.")),
                    Paragraph(Text(
                        "The first rate is the source-to-intermediate height ratio. The second rate is "
                        + "the intermediate-to-target ratio, and normality transports that limit along "
                        + "the first translation. Intermediate height tending to infinity makes the "
                        + "shared factor eventually nonzero, so cancellation identifies the product "
                        + "of the two ratios with the composite ratio.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Tendsto.comp, Tendsto.mul, "
                        + "Tendsto.eventually_gt_atTop, and div_mul_div_cancel_0. No complete exchange-rate "
                        + "composition theorem was found, so the Lean declaration is a thin assembly of "
                        + "those upstream facts."))),
                DescribeRole.Proposition)),
        []));
}
