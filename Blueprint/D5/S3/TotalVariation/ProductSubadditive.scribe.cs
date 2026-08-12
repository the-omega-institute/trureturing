using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ProductSubadditiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total variation is subadditive over finite products under absolute-mass bounds in exactly the two hybrid scaling positions, and the bound is strict on a concrete Bool product.",
        H("Product Subadditivity of Total Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("total-variation-is-subadditive-over-independent-products"),
                DeclarationHandle.Create("D5/S3/TotalVariation/ProductSubadditive.total_variation_product_subadditive"),
                H("Total variation is subadditive over independent products"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Forall, Sp,
                                    F.Id("p"), Apos, Comma, Sp,
                                    F.Id("q"), Apos, Colon, Sp,
                                    Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    Vert, Sp, F.Id("p"), Open, F.Id("i"), Close, Vert,
                                    Sp, Le, Sp, D(1), Sp, Land, Sp,
                                    Sum, Sp, Underscore, Grp(F.Id("k")), Sp,
                                    Vert, Sp, F.Id("q"), Apos, Open, F.Id("k"), Close, Vert,
                                    Sp, Le, Sp, D(1), Close, Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    Open, F.Id("i"), Comma, Sp, F.Id("k"), Close,
                                    Sp, Mapsto, Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Sp, Cdot, Sp,
                                    F.Id("p"), Apos, Open, F.Id("k"), Close, Comma, Sp,
                                    Open, F.Id("i"), Comma, Sp, F.Id("k"), Close,
                                    Sp, Mapsto, Sp,
                                    F.Id("q"), Open, F.Id("i"), Close, Sp, Cdot, Sp,
                                    F.Id("q"), Apos, Open, F.Id("k"), Close, Close,
                                    Sp, Le, Sp, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Plus,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    F.Id("p"), Apos, Comma, Sp, F.Id("q"), Apos, Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For probability laws, the theorem says that running two independent " +
                                        "experiments cannot separate a pair of laws by more than the sum of the " +
                                        "separations available from the two experiments individually. The formal " +
                                        "statement is stronger: its four inputs are arbitrary real-valued " +
                                        "functions subject only to the two displayed absolute-mass bounds.")),
                                    Paragraph(Text(
                                        "The proof inserts the hybrid product p tensor q' between p tensor p' " +
                                        "and q tensor q', then applies the frozen triangle inequality for total " +
                                        "variation. The first leg changes only the second factor, while the " +
                                        "second leg changes only the first. This decomposition exposes exactly " +
                                        "which fixed factor scales each marginal distance.")),
                                    Paragraph(Text(
                                        "The hypotheses are asymmetric, and the asymmetry is forced by the two " +
                                        "collapse identities. The first is TV(p tensor p', p tensor q') = " +
                                        "(sum_i |p(i)|) TV(p',q'), so sum_i |p(i)| <= 1 bounds that leg by " +
                                        "TV(p',q'). The second is TV(p tensor q', q tensor q') = " +
                                        "(sum_k |q'(k)|) TV(p,q), so sum_k |q'(k)| <= 1 bounds that leg by " +
                                        "TV(p,q).")),
                                    Paragraph(Text(
                                        "Thus the hypothesis set consists exactly of the two scaling positions: " +
                                        "p in the first collapse and q' in the second. The other two factors, q " +
                                        "and p', require no hypothesis whatsoever. In particular, the assumptions " +
                                        "are absolute-mass bounds, not normalization conditions; unit mass has " +
                                        "been weakened to absolute mass at most one.")),
                                    Paragraph(Text(
                                        "Pointwise nonnegativity is not required anywhere. Both collapses retain " +
                                        "the absolute masses directly, and the identity abs_mul separates the " +
                                        "absolute value of each product without a sign rewrite. The asymmetric " +
                                        "assumptions are therefore earned by the proof rather than omitted by " +
                                        "oversight."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("product-subadditivity-is-strict-on-a-bool-witness"),
                DeclarationHandle.Create("D5/S3/TotalVariation/ProductSubadditive.total_variation_product_strict"),
                H("Product subadditivity is strict on a Bool witness"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    F.Id("p"), Eq,
                                    Delta, Underscore, Grp(Operatorname, Grp(F.Id("true"))), Comma, RowBreak,
                                    F.Id("q"), Open, Operatorname, Grp(F.Id("true")), Close, Eq,
                                    Frac, Grp(D(1)), Grp(Pi), Comma, Sp,
                                    F.Id("q"), Open, Operatorname, Grp(F.Id("false")), Close, Eq,
                                    D(1), Minus, Frac, Grp(D(1)), Grp(Pi), Comma, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    Open, F.Id("b"), Underscore, Grp(D(1)), Comma, Sp,
                                    F.Id("b"), Underscore, Grp(D(2)), Close, Sp, Mapsto, Sp,
                                    F.Id("p"), Open, F.Id("b"), Underscore, Grp(D(1)), Close,
                                    Sp, Cdot, Sp,
                                    F.Id("p"), Open, F.Id("b"), Underscore, Grp(D(2)), Close, Comma, Sp,
                                    Open, F.Id("b"), Underscore, Grp(D(1)), Comma, Sp,
                                    F.Id("b"), Underscore, Grp(D(2)), Close, Sp, Mapsto, Sp,
                                    F.Id("q"), Open, F.Id("b"), Underscore, Grp(D(1)), Close,
                                    Sp, Cdot, Sp,
                                    F.Id("q"), Open, F.Id("b"), Underscore, Grp(D(2)), Close, Close,
                                    Eq, D(1), Minus,
                                    Frac, Grp(D(1)), Grp(Pi, Caret, Grp(D(2))), Lt,
                                    D(2), Minus, Frac, Grp(D(2)), Grp(Pi), Eq, RowBreak,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Plus,
                                    Operatorname, Grp(F.Id("TV")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Comma, RowBreak,
                                    Open, D(2), Minus, Frac, Grp(D(2)), Grp(Pi), Close, Minus,
                                    Open, D(1), Minus,
                                    Frac, Grp(D(1)), Grp(Pi, Caret, Grp(D(2))), Close, Eq,
                                    Open, D(1), Minus, Frac, Grp(D(1)), Grp(Pi), Close,
                                    Caret, Grp(D(2)), Gt, Sp, D(0), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The strictness witness is the mathematical content that distinguishes " +
                                        "product behavior here. Renyi divergence is exactly additive over " +
                                        "products, whereas total variation is only subadditive; the weak " +
                                        "inequality alone would not reveal that distinction.")),
                                    Paragraph(Text(
                                        "On Bool, let p be the point mass at true and let q assign 1/pi to true " +
                                        "and 1-1/pi to false. Each of the two identical marginal comparisons has " +
                                        "total variation 1-1/pi. Their product comparison has total variation " +
                                        "1-1/pi^2, while the sum of the marginal total variations is 2-2/pi.")),
                                    Paragraph(Text(
                                        "Consequently the difference between the right and left sides is " +
                                        "(2-2/pi)-(1-1/pi^2) = (1-1/pi)^2. Since pi > 1, this perfect square is " +
                                        "strictly positive. The formal theorem proves the resulting strict " +
                                        "inequality for the concrete Bool product rather than merely recording a " +
                                        "numerical example.")),
                                    Paragraph(Text(
                                        "No n-fold product or i.i.d. specialization " +
                                        "is claimed. The module gives no characterization of equality, no reverse " +
                                        "inequality, and no measure-theoretic analogue."))),
                DescribeRole.Theorem
            ))));
}
