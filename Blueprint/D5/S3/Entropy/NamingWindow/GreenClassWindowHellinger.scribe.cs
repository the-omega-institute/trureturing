using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class GreenClassWindowHellingerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite naming-window Bhattacharyya affinity factors across coordinates, giving an " +
        "exact product-defect formula and a coordinate-sum bound for squared Hellinger distance.",
        H("Green-Class Window Hellinger Structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-affinity-is-the-coordinate-product"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.bhattacharyya_windowLaw"),
                H("Window affinity is the product of coordinate affinities"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("BC")), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close,
                    Sp, Eq, Sp,
                    Prod, Underscore, Grp(F.Id("i")), Sp,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("i")), Comma, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When every coordinate radicand p_i(a)q_i(a) is nonnegative, the square " +
                        "root of the window product is the product of the coordinate square " +
                        "roots. Finite sum-product factorization then gives one affinity factor " +
                        "per coordinate.")),
                    Paragraph(Text(
                        "The hypothesis follows the asymmetric signature of Real.sqrt_prod. No " +
                        "normalization is required for this multiplicative identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-hellinger-square-is-a-product-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.hellingerSq_windowLaw_product_defect"),
                H("Window Hellinger square is an exact product defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close,
                    Sp, Eq, Sp, D(2), Sp, Times, Sp, Open, D(1), Minus,
                    Prod, Underscore, Grp(F.Id("i")), Sp, Open, D(1), Minus,
                    Frac,
                    Grp(F.Id("H"), Caret, Grp(D(2)), Open,
                        F.Id("p"), Underscore, Grp(F.Id("i")), Comma, Sp,
                        F.Id("q"), Underscore, Grp(F.Id("i")), Close),
                    Grp(D(2)), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonnegative normalized coordinate laws, each coordinate affinity is " +
                        "one minus half its squared Hellinger distance. Window affinity " +
                        "multiplicativity therefore turns the probability Hellinger identity " +
                        "into the displayed product defect.")),
                    Paragraph(Text(
                        "The product law is exact, including the empty coordinate family. It " +
                        "records the interaction term that prevents squared Hellinger distance " +
                        "from being additive on independent windows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-hellinger-square-is-bounded-by-the-coordinate-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/GreenClassWindowHellinger.hellingerSq_windowLaw_le_sum"),
                H("Window Hellinger square is bounded by the coordinate sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("p"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("windowLaw")), Open, F.Id("q"), Close, Close,
                    Sp, Le, Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Underscore, Grp(F.Id("i")), Comma, Sp,
                    F.Id("q"), Underscore, Grp(F.Id("i")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Half of every coordinate Hellinger square lies in the unit interval. " +
                        "Induction over the finite coordinate set proves that one minus the " +
                        "product of the complementary factors is at most their sum.")),
                    Paragraph(Text(
                        "Applying that elementary product-defect inequality to the exact window " +
                        "formula yields the coordinate-sum upper bound. Equality is not claimed; " +
                        "the omitted mixed defect terms are generally nonzero."))),
                DescribeRole.Theorem))));
}
