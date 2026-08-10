using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class MonotoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/RenyiDivergence/Monotone",
            "Finite Renyi divergence is nondecreasing in its order separately below and above order one under minimal reference-mass hypotheses."),
        H("Order Monotonicity of Finite Renyi Divergence"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-renyi-divergence-is-monotone-below-order-one"),
                H("Finite Renyi divergence is monotone below order one"),
                LeanTheorem(
                    "D5/S3/RenyiDivergence/Monotone.renyi_divergence_monotone_of_lt_one"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, Comma, Sp, Beta, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Lt, Sp, Alpha, Sp, Le, Sp, Beta, Sp, Lt, Sp, D(1), Comma,
                    RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Le, Sp,
                    F.Id("D"), Underscore, Grp(Beta, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The theorem supplies monotonicity in the order on the interval strictly " +
                        "below one: if 0 < alpha <= beta < 1, then D_alpha(p||q) <= " +
                        "D_beta(p||q). Together with the super-unit theorem below, this is the " +
                        "property that makes the Renyi family a coherent scale rather than a " +
                        "collection of unrelated quantities. The bucket's domain registration " +
                        "promised order monotonicity, and these two theorems supply it on the " +
                        "ranges where it genuinely holds under the repository's conventions.")),
                    Paragraph(Text(
                        "The hypotheses are weaker than a conventional probability-law statement " +
                        "may suggest. Only p is required to be pointwise nonnegative and " +
                        "normalized. The reference mass q need only be pointwise nonnegative; it " +
                        "is not required to be normalized, and no discrete absolute-continuity " +
                        "hypothesis is imposed. Eleven waves in this bucket have now shown that " +
                        "deriving hypotheses statement by statement, rather than copying a " +
                        "sibling's assumptions, yields strictly stronger results.")),
                    Paragraph(Text(
                        "Write S_gamma = sum_i p(i)^gamma q(i)^(1-gamma). Below one, both shifted " +
                        "orders alpha-1 and beta-1 are negative, and the ratio " +
                        "r = (alpha-1)/(beta-1) is at least one. Weighted Jensen gives " +
                        "S_beta^r <= S_alpha. After taking logarithms, division by the negative " +
                        "quantity alpha-1 reverses the inequality and yields " +
                        "D_alpha(p||q) <= D_beta(p||q). If the supports do not overlap, both " +
                        "power sums and both totalized divergences are zero; otherwise positivity " +
                        "licenses the logarithmic step.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-renyi-divergence-is-monotone-above-order-one"),
                H("Finite Renyi divergence is monotone above order one"),
                LeanTheorem(
                    "D5/S3/RenyiDivergence/Monotone.renyi_divergence_monotone_of_one_lt"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, Comma, Sp, Beta, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(1), Lt, Sp, Alpha, Sp, Le, Sp, Beta, Sp, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Le, Sp,
                    F.Id("D"), Underscore, Grp(Beta, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Above one, the shifted orders are positive and the same Jensen mechanism " +
                        "uses the ratio in the opposite direction: " +
                        "r = (beta-1)/(alpha-1) >= 1 gives S_alpha^r <= S_beta. Division by the " +
                        "positive quantity beta-1 preserves the direction and again yields " +
                        "D_alpha(p||q) <= D_beta(p||q). Thus the sign change at one is handled " +
                        "symmetrically by reversing the ratio, rather than by adjoining an " +
                        "unrelated inequality argument. At alpha = 1 the prefactor 1/(alpha-1) " +
                        "is totalized to zero altogether, which is exactly why that endpoint " +
                        "cannot be included.")),
                    Paragraph(Text(
                        "The scope divides into three categories and must not be compressed into " +
                        "a proved-versus-unproved dichotomy.")),
                    Paragraph(Text(
                        "PROVED. Monotonicity holds for 0 < alpha <= beta < 1 and for " +
                        "1 < alpha <= beta, with p normalized and nonnegative and q only " +
                        "pointwise nonnegative.")),
                    Paragraph(Text(
                        "DISPROVED under the repository's literal conventions. Including beta = 1 " +
                        "fails: a point mass p against a uniform q has D_(1/2)(p||q) = log 2 but " +
                        "D_1(p||q) = 0, because totalization sends the prefactor 1/(alpha-1) to " +
                        "zero at alpha = 1 and thereby destroys the limiting divergence value. " +
                        "The unrestricted straddling claim also fails: a uniform p against a " +
                        "point-mass q has D_(1/2)(p||q) = log 2 but " +
                        "D_2(p||q) = -2 log 2.")),
                    Paragraph(Text(
                        "The straddling counterexample is produced entirely by the totalizing " +
                        "conventions. At a coordinate where q vanishes and p does not, the term " +
                        "p^2/q is mathematically infinite, whereas Lean's x/0 = 0 renders it as " +
                        "zero; that erased contribution is what drags D_2 below D_(1/2). This " +
                        "failure is an artifact of the formalization's totality, not a fact about " +
                        "Renyi divergence.")),
                    Paragraph(Text(
                        "NOT PROVED AND NOT DISPROVED. The straddling case with the discrete " +
                        "absolute-continuity hypothesis q(i) = 0 implies p(i) = 0 remains open in " +
                        "this module. That hypothesis removes the counterexample above, but the " +
                        "module establishes no theorem or counterexample for the resulting claim.")),
                    Paragraph(Text(
                        "No order-one limit to the classical divergence, straddling monotonicity " +
                        "under absolute continuity, strictness, data-processing inequality for the " +
                        "Renyi family, or measure-theoretic analogue is claimed. All logarithms " +
                        "are natural, so the units are nats.")))))));
}
