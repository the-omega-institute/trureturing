using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class OrderLimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite, limit-free comparisons of Renyi divergence with its supremum-ratio ceiling and KL order member.",
        H("Finite Order Comparisons for Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("renyi-divergence-is-bounded-by-the-logarithmic-supremum-ratio"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_le_log_sup_ratio"),
                H("Renyi divergence is bounded by the logarithmic supremum ratio"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Nonempty")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    D(1), Lt, Sp, Alpha, Comma, RowBreak,
                    Open,
                    Open,
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Rightarrow, Sp, D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Close, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Le, Sp, Log, Sp, Open,
                    Operatorname, Grp(F.Id("sup")), Underscore, Grp(F.Id("i")), Open,
                    F.Id("p"), Open, F.Id("i"), Close, Slash, F.Id("q"), Open, F.Id("i"), Close,
                    Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For alpha > 1, the finite Renyi divergence is at most the logarithm of the " +
                        "largest likelihood ratio p(i)/q(i). This is the finite, limit-free content " +
                        "of the phrase alpha -> infinity: it gives a usable supremum-ratio ceiling " +
                        "without asserting that any topological limit exists.")),
                    Paragraph(Text(
                        "The proof rewrites the power sum as the p-weighted moment of the likelihood " +
                        "ratio, bounds every ratio by its finite supremum, and then uses monotonicity " +
                        "of real powers and logarithms. Normalized nonnegative p supplies a positive " +
                        "support coordinate; the hypothesis on q makes the relevant ratios positive.")),
                    Paragraph(Text(
                        "The supremum is a Finset supremum over the finite index type, not a newly named " +
                        "max-divergence. The theorem therefore remains entirely inside the existing " +
                        "totalized finite formula and introduces no additional object or variational " +
                        "characterization."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-renyi-logarithmic-moment-dominates-kl"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/OrderLimits.renyi_log_moment_ge_kl"),
                H("The Renyi logarithmic moment dominates KL"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    Close, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Lt, Sp, Alpha, Comma, RowBreak,
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
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Rightarrow, Sp, D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Rightarrow, RowBreak,
                    Open, Alpha, Minus, D(1), Close, Sp, Star, Sp,
                    Operatorname, Grp(F.Id("klDivergence")), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Le, Sp, Log, Sp, Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Caret, Grp(Alpha, Sp), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Caret, Grp(D(1), Minus, Alpha), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This logarithmic moment inequality is the Jensen step underlying both " +
                        "comparisons with Kullback--Leibler divergence. It relates the finite power " +
                        "sum to KL before any division by alpha - 1, so the sign of that denominator " +
                        "can be handled explicitly in the two order ranges.")),
                    Paragraph(Text(
                        "On the positive support of p, the likelihood ratio is positive by the stated " +
                        "reference-mass condition. Concavity of the logarithm with p as the normalized " +
                        "weight yields (alpha - 1) * KL <= log of the power sum. Coordinates outside " +
                        "the support contribute zero and are removed by the finite-support rewrite.")),
                    Paragraph(Text(
                        "The result is a structural inequality, not an order-one identification. In " +
                        "particular, it does not turn Lean's totalized alpha = 1 value into KL."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("below-one-renyi-divergence-is-at-most-kl"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_le_kl_of_lt_one"),
                H("Below one, Renyi divergence is at most KL"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    Close, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, D(0), Lt, Sp, Alpha, Sp, Land, Sp, Alpha, Lt, Sp, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Rightarrow, Sp, D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Le, Sp, Operatorname, Grp(F.Id("klDivergence")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 0 < alpha < 1, the finite Renyi divergence is at most KL divergence under " +
                        "the same nonnegative normalized p and positive-on-p-support q hypotheses. " +
                        "This is one half of the finite comparison around order one.")),
                    Paragraph(Text(
                        "Jensen first gives (alpha - 1) * KL <= the logarithmic power sum. Because " +
                        "alpha - 1 is negative below one, dividing by it reverses the inequality. " +
                        "That sign flip is why the sub-one statement is a separate theorem rather " +
                        "than an unqualified symmetric slogan.")),
                    Paragraph(Text(
                        "The theorem says nothing about a topological limit as alpha approaches one; it " +
                        "is a pointwise finite inequality for each admissible alpha."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("above-one-kl-is-at-most-renyi-divergence"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/OrderLimits.kl_le_renyi_divergence_of_one_lt"),
                H("Above one, KL is at most Renyi divergence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    Close, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    D(1), Lt, Sp, Alpha, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Rightarrow, Sp, D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("klDivergence")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Le, Sp, F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For alpha > 1, KL divergence is at most the finite Renyi divergence at order " +
                        "alpha. It is the super-one counterpart to the preceding comparison and uses " +
                        "exactly the same finite logarithmic moment inequality.")),
                    Paragraph(Text(
                        "Here alpha - 1 is positive, so division preserves the Jensen direction. The " +
                        "single denominator sign change explains the split into below-one and above-one " +
                        "theorems: Jensen supplies the common engine, while order determines the final " +
                        "inequality direction.")),
                    Paragraph(Text(
                        "This is a comparison with the KL expression as a finite order member. It does " +
                        "not identify the totalized order-one value of Renyi divergence with KL and does " +
                        "not establish convergence to it."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("half-order-renyi-divergence-is-at-most-kl"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/OrderLimits.renyi_divergence_one_half_le_kl"),
                H("The half-order Renyi divergence is at most KL"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    Close, Comma, RowBreak,
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
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Rightarrow, Sp, D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Rightarrow, RowBreak,
                    Minus, D(2), Sp, Star, Sp, Log, Sp, Open,
                    Operatorname, Grp(F.Id("bhattacharyya")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Close,
                    Le, Sp, Operatorname, Grp(F.Id("klDivergence")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At alpha = 1/2, the below-one comparison specializes to the frozen " +
                        "Bhattacharyya expression: minus twice the logarithm of the Bhattacharyya " +
                        "coefficient is at most KL divergence. This records consistency with the " +
                        "already established half-order result rather than introducing a new notion.")),
                    Paragraph(Text(
                        "The specialization keeps the same support assumptions as the general below-one " +
                        "theorem. Positive q on the positive support of p makes the logarithmic moment " +
                        "argument finite under the repository's totalized real operations.")),
                    Paragraph(Text(
                        "The four narrative points are deliberate. The bucket previously had order " +
                        "monotonicity, power and product additivity, data processing, the half-order " +
                        "case, nonnegativity, and self-zero, but nothing relating the family to its " +
                        "limiting members; that gap was found by reading the existing declaration list, " +
                        "not by guessing from this title.")),
                    Paragraph(Text(
                        "The results here are stated without limits deliberately. Alpha -> infinity is " +
                        "represented by a finite supremum-ratio ceiling, and alpha -> 1 by two-sided " +
                        "comparison with KL. There is no topology, no tendsto statement, and nothing is " +
                        "named as a limit, because no limit is proved.")),
                    Paragraph(Text(
                        "What is not proved is equally important: no topological limit at infinity or at " +
                        "one, no named max-divergence, no variational formula, and no identification of " +
                        "the totalized order-one value with KL. That last step can look obvious, but it " +
                        "requires its own proof and is intentionally absent from the Lean module."))),
                DescribeRole.Theorem
            )
        )));
}
