using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class ProductAdditivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite Renyi divergence is additive on products of nonnegative finite mass functions with nonvanishing marginal power sums at every real order.",
        H("Product Additivity of Finite Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-renyi-divergence-is-additive-on-products"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/ProductAdditivity.renyi_divergence_product_additive"),
                H("Finite Renyi divergence is additive on products"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("p"), Apos, Comma, Sp, F.Id("q"), Apos, Colon, Sp,
                    Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Apos, Open, F.Id("j"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Apos, Open, F.Id("j"), Close, Close,
                    Sp, Land, Sp, RowBreak,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    Caret, Grp(Alpha, Sp), Sp,
                    F.Id("q"), Open, F.Id("i"), Close,
                    Caret, Grp(D(1), Minus, Alpha, Sp), Close,
                    Neq, Sp, D(0),
                    Sp, Land, Sp, RowBreak,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("j")), Sp,
                    F.Id("p"), Apos, Open, F.Id("j"), Close,
                    Caret, Grp(Alpha, Sp), Sp,
                    F.Id("q"), Apos, Open, F.Id("j"), Close,
                    Caret, Grp(D(1), Minus, Alpha, Sp), Close,
                    Neq, Sp, D(0), Close,
                    Close, Sp, Rightarrow, Sp, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    F.Id("p"), Apos, Open, F.Id("j"), Close,
                    Vert, Sp, Vert, Sp,
                    Open, F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Mapsto, Sp,
                    F.Id("q"), Open, F.Id("i"), Close,
                    F.Id("q"), Apos, Open, F.Id("j"), Close,
                    Close, Eq, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Plus,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Apos, Vert, Sp, Vert, Sp,
                    F.Id("q"), Apos, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Independent finite experiments add their Renyi divergences. This " +
                        "product law is what makes the family behave as an information measure " +
                        "across independent structure, and it is the Renyi counterpart of the " +
                        "frozen classical theorem kl_divergence_product_additive.")),
                    Paragraph(Text(
                        "The hypotheses are strictly weaker than those of that classical " +
                        "analogue. The classical theorem requires every coordinate of all four " +
                        "mass functions to be strictly positive and normalizes the two first " +
                        "distributions. Here all four functions need only be pointwise " +
                        "nonnegative, and the two marginal power sums need only be nonzero. No " +
                        "normalization is required. Zero coordinates are permitted provided " +
                        "each marginal power sum remains nonzero. This weakening is available " +
                        "because Real.rpow is well defined on nonnegative arguments, whereas " +
                        "the classical proof takes the logarithm of a ratio.")),
                    Paragraph(Text(
                        "The proof first applies Real.mul_rpow to split each joint summand into " +
                        "the product of its two marginal summands. Fintype.sum_prod_type exposes " +
                        "the iterated finite sum, and Fintype.sum_mul_sum factors it as the " +
                        "product of the two marginal power sums. Real.log_mul then splits the " +
                        "joint logarithm, after which the shared prefactor distributes over the " +
                        "sum.")),
                    Paragraph(Text(
                        "The prefactor 1/(alpha-1) imposes no order restriction here. In the " +
                        "monotonicity and data-processing results, its sign changes across " +
                        "alpha = 1, reverses inequalities below one, and makes a straddling " +
                        "claim false. Product additivity is instead an equality: the same " +
                        "prefactor multiplies the joint logarithm and both marginal logarithms, " +
                        "so it distributes algebraically rather than reversing an inequality. " +
                        "The theorem consequently holds for every real alpha, below and above " +
                        "one alike. It also holds literally at alpha = 1, where totalized real " +
                        "division makes the prefactor zero and both sides vanish.")),
                    Paragraph(Text(
                        "The two non-vanishing assumptions are forced by the single " +
                        "Real.log_mul step. Without them, the convention Real.log 0 = 0 does " +
                        "not satisfy log(0*y) = log 0 + log y: when one marginal power sum " +
                        "vanishes, factorization can therefore turn a false divergence identity " +
                        "into an apparently formal logarithmic split. The stated hypotheses are " +
                        "exactly what Real.log_mul requires, rather than a positive-overlap " +
                        "condition, which would be stronger than necessary.")),
                    Paragraph(Text(
                        "No n-fold product or i.i.d. form, sample-complexity corollary, " +
                        "order-one limit, or measure-theoretic analogue is claimed. All " +
                        "logarithms are natural, so the units are nats."))),
                DescribeRole.Theorem))));
}
