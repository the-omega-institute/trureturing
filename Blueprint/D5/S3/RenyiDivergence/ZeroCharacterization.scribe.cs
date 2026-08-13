using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class ZeroCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Renyi divergence is nonnegative above order one and vanishes exactly when the two normalized laws coincide, with deliberately different support hypotheses below and above one.",
        H("Zero Characterization of Finite Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-renyi-divergence-is-nonnegative-above-one-under-absolute-continuity"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_nonneg_of_one_lt"),
                H("Finite Renyi divergence is nonnegative above one under absolute continuity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    D(1), Lt, Sp, Alpha, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(0), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    D(0), Le, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen Basic module proved zero self-divergence at every real order, " +
                        "but its nonnegativity theorem covered only 0 < alpha < 1. This declaration " +
                        "supplies the missing super-unit half under discrete absolute continuity: " +
                        "every zero coordinate of q is also a zero coordinate of p.")),
                    Paragraph(Text(
                        "Above one the proof is a composition of frozen results. Kullback--Leibler " +
                        "divergence is nonnegative, and the frozen comparison gives KL(p || q) <= " +
                        "D_alpha(p || q); transitivity therefore yields the claimed lower bound.")),
                    Paragraph(Text(
                        "Absolute continuity is load-bearing rather than decorative. The preceding " +
                        "wave already compiled the order-two witness p = (1/2, 1/2), q = (1, 0), " +
                        "whose divergence is -2 log 2 because the repository's totalization sends " +
                        "a zero base with a negative exponent to zero rather than infinity. This " +
                        "declaration does not repeat that witness; it supplies the hypothesis that " +
                        "excludes its support boundary.")),
                    Paragraph(Text(
                        "The authored display is legal because no pinned projectable statement " +
                        "fixture exists for this declaration; construction records the resulting " +
                        "ProjectionGap."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("below-one-zero-renyi-divergence-characterizes-equality-under-common-positive-support"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff_of_lt_one"),
                H("Below one, zero Renyi divergence characterizes equality under common positive support"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    D(0), Lt, Sp, Alpha, Sp, Land, Sp, Alpha, Lt, Sp, D(1), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Exists, Sp, F.Id("i"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("i"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
                    F.Id("p"), Eq, Sp, F.Id("q"), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The bucket previously had no converse to zero self-divergence: nowhere did " +
                        "a vanishing Renyi divergence force the two laws to coincide. Below one this " +
                        "declaration supplies that converse under the existence of one coordinate " +
                        "where both p and q are strictly positive.")),
                    Paragraph(Text(
                        "This side requires a genuine equality argument because the frozen KL " +
                        "comparison points the wrong way, D_alpha(p || q) <= KL(p || q), and hence " +
                        "a zero Renyi divergence gives no KL upper bound. Vanishing first forces the " +
                        "positive power sum to equal one. Weighted arithmetic--geometric mean bounds " +
                        "each summand by alpha p_i + (1 - alpha) q_i, whose normalized finite sum is " +
                        "also one. Equality of these two finite sums forces equality at every " +
                        "coordinate, and mathlib's weighted AM--GM equality condition " +
                        "Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos then gives p_i = q_i.")),
                    Paragraph(Text(
                        "Common positive support is deliberately weaker than absolute continuity. " +
                        "Only one shared positive coordinate is needed to keep the power sum " +
                        "strictly positive and recover it from its logarithm; no implication from " +
                        "every zero of q to a zero of p is assumed. Consequently this below-one " +
                        "statement is stronger in its support generality than the above-one result.")),
                    Paragraph(Text(
                        "The authored display is legal because no pinned projectable statement " +
                        "fixture exists for this declaration; construction records the resulting " +
                        "ProjectionGap."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("above-one-zero-renyi-divergence-characterizes-equality-under-absolute-continuity"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff_of_one_lt"),
                H("Above one, zero Renyi divergence characterizes equality under absolute continuity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    D(1), Lt, Sp, Alpha, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(0), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
                    F.Id("p"), Eq, Sp, F.Id("q"), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Above one the equality characterization is substantially cheaper than its " +
                        "below-one counterpart. Nonnegativity gives 0 <= KL(p || q), while the frozen " +
                        "super-unit comparison gives KL(p || q) <= D_alpha(p || q). If the Renyi " +
                        "divergence vanishes, these inequalities squeeze KL to zero, and the frozen " +
                        "kl_divergence_eq_zero_iff theorem yields p = q. The reverse implication is " +
                        "the already frozen self-divergence theorem.")),
                    Paragraph(Text(
                        "The proof uses absolute continuity twice through the frozen KL material: it " +
                        "supports KL nonnegativity and converts positivity of p into positivity of q " +
                        "where the order comparison needs it. The weaker common-positive-support " +
                        "premise from the below-one theorem cannot replace this condition.")),
                    Paragraph(Text(
                        "Thus the two sides do not carry identical hypotheses or proof costs. Above " +
                        "one is a composition of frozen KL results under the stronger support law; " +
                        "below one is a coordinatewise AM--GM equality proof under the weaker shared " +
                        "positivity assumption.")),
                    Paragraph(Text(
                        "The authored display is legal because no pinned projectable statement " +
                        "fixture exists for this declaration; construction records the resulting " +
                        "ProjectionGap."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("at-positive-orders-other-than-one-zero-renyi-divergence-characterizes-equality-under-absolute-continuity"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/ZeroCharacterization.renyi_divergence_eq_zero_iff"),
                H("At positive orders other than one, zero Renyi divergence characterizes equality under absolute continuity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    D(0), Lt, Sp, Alpha, Sp, Land, Sp, Alpha, Neq, Sp, D(1), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(1), Sp, Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(0), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
                    F.Id("p"), Eq, Sp, F.Id("q"), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the unified entry point for every positive order other than one. " +
                        "The exclusion is necessary because the literal totalized definition has " +
                        "value zero at order one for every pair. Together with the preceding " +
                        "nonnegativity result, it completes the missing above-one sign statement and " +
                        "the converse to zero self-divergence on both sides of one.")),
                    Paragraph(Text(
                        "The unified statement deliberately pays the stronger absolute-continuity " +
                        "hypothesis in order to use one condition on both branches. Under " +
                        "normalization, absolute continuity implies common positive support: some " +
                        "coordinate has p_i > 0, and the contrapositive of absolute continuity makes " +
                        "q_i nonzero there, hence positive by nonnegativity. The converse implication " +
                        "fails in general, so this combined theorem does not erase the greater " +
                        "support generality of the dedicated below-one result.")),
                    Paragraph(Text(
                        "When alpha < 1, the derived common positive coordinate feeds the weighted " +
                        "AM--GM characterization. When alpha > 1, the theorem invokes the KL squeeze. " +
                        "The case split therefore unifies the conclusion without pretending that the " +
                        "two proof mechanisms or their minimal hypotheses are the same.")),
                    Paragraph(Text(
                        "The authored display is legal because no pinned projectable statement " +
                        "fixture exists for this declaration; construction records the resulting " +
                        "ProjectionGap."))),
                DescribeRole.Theorem
            )
        )));
}
