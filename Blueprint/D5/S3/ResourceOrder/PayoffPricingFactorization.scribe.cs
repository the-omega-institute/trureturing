using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class PayoffPricingFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear price descends uniquely to attainable payoffs exactly when it kills null trades.",
        H("Payoff Pricing Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("payoff-price-factorization-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PayoffPricingFactorization"
                    + ".payoff_price_factorization_iff"),
                H("Prices factor uniquely through payoff range"),
                StatementSource.FromAuthor(PayoffFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let payoff and price be linear maps on the same trade module. Equal "
                        + "payoffs receive equal prices exactly when every null-payoff trade also "
                        + "has zero price, expressed by inclusion of the two kernels.")),
                    Paragraph(Text(
                        "That kernel inclusion is also exactly the condition for price to factor "
                        + "through the attainable payoff range. The factor is unique because every "
                        + "element of the range has a trade witness, so agreement on all payoffs "
                        + "determines the linear map everywhere.")),
                    Paragraph(Text(
                        "Pinned Mathlib source search found the reusable first-isomorphism "
                        + "infrastructure Submodule.liftQ, LinearMap.quotKerEquivRange, and "
                        + "LinearMap.quotKerEquivRange_symm_apply_image, but no declaration "
                        + "combining the displayed equivalences. Local smart-search declaration-name "
                        + "queries returned no exact hit. NyxID exposed no Loogle or LeanSearch "
                        + "service, so those endpoints are not counted as negative searches. A "
                        + "Tavily/GitHub search succeeded after an initial HTTP 422 caused by a "
                        + "missing Content-Type header and likewise found only the first-isomorphism "
                        + "infrastructure, not the combined theorem.")),
                    Paragraph(Text(
                        "This closes exactly the displayed three-condition theorem in qdo-v1 "
                        + "theorem/34.3, atom "
                        + "qdo-residual-325e585194898f14ad5f72c580d596555f450f13d59ffb121c471def9d8513c5. "
                        + "No surrounding economic interpretation is claimed as a separate theorem."))),
                DescribeRole.Theorem))));

    private static Formula LinearMap(Formula source, Formula target) => Seq(
        Operatorname, Grp(F.Id("LinearMap")), Underscore, Grp(F.Id("R")),
        Open, source, Comma, Sp, target, Close);

    private static Formula Apply(Formula map, Formula value) =>
        Seq(map, Open, value, Close);

    private static Formula Kernel(Formula map) => Seq(Ker, Sp, map);

    private static Formula PayoffFactorizationFormula()
    {
        Formula payoff = F.Id("payoff");
        Formula price = F.Id("price");
        Formula z = F.Id("z");
        Formula zPrime = F.Id("zPrime");

        return Disp(Seq(
            payoff, Colon, Sp, LinearMap(F.Id("M"), F.Id("N")), Comma, Sp,
            price, Colon, Sp, LinearMap(F.Id("M"), F.Id("R")), Comma, Esc,
            Open,
            Open, Forall, Sp, z, Comma, Sp, zPrime, Comma, Sp,
            Apply(payoff, z), Sp, Eq, Sp, Apply(payoff, zPrime), Sp,
            Rightarrow, Sp, Apply(price, z), Sp, Eq, Sp, Apply(price, zPrime), Close,
            Sp, Leftrightarrow, Sp,
            Kernel(payoff), Sp, Subseteq, Sp, Kernel(price),
            Close, Sp, Land, Sp,
            Open,
            Kernel(payoff), Sp, Subseteq, Sp, Kernel(price), Sp,
            Leftrightarrow, Sp,
            Exists, Bang, Sp, F.Id("factor"), Colon, Sp,
            LinearMap(Seq(Operatorname, Grp(F.Id("range")), Open, payoff, Close), F.Id("R")),
            Comma, Sp, Forall, Sp, z, Comma, Sp,
            Apply(price, z), Sp, Eq, Sp,
            Apply(F.Id("factor"), Apply(payoff, z)),
            Close, Dot));
    }
}
