using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ConvexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/TotalVariation/Convexity",
            "Total variation is jointly convex without mass hypotheses, while squared Hellinger distance is jointly convex on the nonnegative quadrant."),
        H("Joint Convexity of Total Variation and Squared Hellinger Distance"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("total-variation-is-jointly-convex-for-arbitrary-real-functions"),
                H("Total variation is jointly convex for arbitrary real functions"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Convexity.total_variation_joint_convex"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("p"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("t"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, D(0), Le, Sp, F.Id("t"), Sp, Land, Sp,
                    F.Id("t"), Le, Sp, D(1), Close, Sp, Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("t"), Sp, F.Id("p"), Underscore, Grp(D(1)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("t"), Sp, F.Id("q"), Underscore, Grp(D(1)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Close, Le, Sp, RowBreak,
                    F.Id("t"), Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Close, Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The repository already established joint convexity for " +
                        "Kullback--Leibler divergence. The present total-variation theorem and " +
                        "the squared-Hellinger theorem below complete the corresponding picture " +
                        "for the statistical distances developed here: mixing two pairs of laws " +
                        "cannot leave their mixed separation above the weighted average of the " +
                        "two endpoint separations.")),
                    Paragraph(Text(
                        "The three joint-convexity statements expose a precise hierarchy of " +
                        "hypotheses. Finite Kullback--Leibler divergence, measured in nats, " +
                        "requires pointwise nonnegativity and discrete absolute continuity. Its " +
                        "definition contains both division and the natural logarithm. In Lean's " +
                        "totalized arithmetic, positive source mass over zero reference mass " +
                        "would be flattened by division by zero and the ensuing logarithm at " +
                        "zero; the support condition excludes exactly this false finite-cost " +
                        "case.")),
                    Paragraph(Text(
                        "Total variation contains neither operation. It uses only coordinatewise " +
                        "absolute values and a finite sum, so the theorem assumes nothing at all " +
                        "about the four mass functions: they may be arbitrary real-valued " +
                        "functions. The sole hypothesis is 0 <= t <= 1, and it enters only to " +
                        "replace |t| by t and |1-t| by 1-t in the absolute-value triangle " +
                        "inequality. The caller separately verified this advertised generality " +
                        "by applying the theorem to functions taking negative values.")),
                    Paragraph(Text(
                        "Squared Hellinger distance likewise contains no division and no " +
                        "logarithm, so it pays no support condition. It does, however, use square " +
                        "roots. The squared square-root gap is jointly convex only on the " +
                        "nonnegative quadrant, and this geometric step alone forces pointwise " +
                        "nonnegativity of all four functions. Thus every hypothesis in the three " +
                        "results is charged to a specific operation in the corresponding " +
                        "definition: absolute value costs only nonnegative mixing weights, square " +
                        "root costs the nonnegative quadrant, and division with logarithm also " +
                        "costs discrete absolute continuity.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-squared-square-root-gap-is-jointly-convex-under-mixing"),
                H("The squared square-root gap is jointly convex under mixing"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Convexity.sq_sqrt_mix_sub_sqrt_mix_le"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp,
                    F.Id("a"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("a"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("b"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("b"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("t"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, D(0), Le, Sp, F.Id("t"), Sp, Land, Sp,
                    F.Id("t"), Le, Sp, D(1), Close, Sp, Land, RowBreak,
                    Open,
                    D(0), Le, Sp, F.Id("a"), Underscore, Grp(D(1)), Sp, Land, Sp,
                    D(0), Le, Sp, F.Id("a"), Underscore, Grp(D(2)), Sp, Land, Sp,
                    D(0), Le, Sp, F.Id("b"), Underscore, Grp(D(1)), Sp, Land, Sp,
                    D(0), Le, Sp, F.Id("b"), Underscore, Grp(D(2)), Close,
                    Sp, Rightarrow, RowBreak,
                    Open,
                    Sqrt, Sp, Grp(
                        F.Id("t"), Sp, F.Id("a"), Underscore, Grp(D(1)), Plus,
                        Open, D(1), Minus, F.Id("t"), Close, Sp,
                        F.Id("a"), Underscore, Grp(D(2))), Minus,
                    Sqrt, Sp, Grp(
                        F.Id("t"), Sp, F.Id("b"), Underscore, Grp(D(1)), Plus,
                        Open, D(1), Minus, F.Id("t"), Close, Sp,
                        F.Id("b"), Underscore, Grp(D(2))),
                    Close, Caret, Grp(D(2)), Le, Sp, RowBreak,
                    F.Id("t"), Sp, Open,
                    Sqrt, Sp, Grp(F.Id("a"), Underscore, Grp(D(1))), Minus,
                    Sqrt, Sp, Grp(F.Id("b"), Underscore, Grp(D(1))),
                    Close, Caret, Grp(D(2)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp, Open,
                    Sqrt, Sp, Grp(F.Id("a"), Underscore, Grp(D(2))), Minus,
                    Sqrt, Sp, Grp(F.Id("b"), Underscore, Grp(D(2))),
                    Close, Caret, Grp(D(2)), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The named scalar lemma sq_sqrt_mix_sub_sqrt_mix_le carries the " +
                        "Hellinger half of the module. It compares the squared square-root gap of " +
                        "two mixtures with the corresponding mixture of squared endpoint gaps. " +
                        "The finite-dimensional theorem below is obtained by applying this result " +
                        "coordinatewise and summing.")),
                    Paragraph(Text(
                        "The pinned mathlib supplies the one-variable theorem " +
                        "Real.strictConcaveOn_sqrt and the finite Cauchy--Schwarz inequality " +
                        "Real.sum_sqrt_mul_sqrt_le, but its searched API contains no concavity " +
                        "theorem for the two-variable geometric mean (a,b) |-> sqrt(a b). The " +
                        "missing two-variable statement is the actual scalar content needed here, " +
                        "so it is proved in this module rather than imported.")),
                    Paragraph(Text(
                        "The proof specializes the finite Cauchy--Schwarz inequality to the two " +
                        "mixing components, obtaining concavity of the geometric-mean cross term. " +
                        "After expanding each squared square-root difference, linear terms agree " +
                        "and that cross-term inequality gives the result. Naming the lemma as a " +
                        "standalone reusable theorem records the unavailable library fact and " +
                        "keeps it from being buried inside the finite-sum convexity proof.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("squared-hellinger-distance-is-jointly-convex-on-the-nonnegative-quadrant"),
                H("Squared Hellinger distance is jointly convex on the nonnegative quadrant"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Convexity.hellinger_sq_joint_convex"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("p"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("t"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, D(0), Le, Sp, F.Id("t"), Sp, Land, Sp,
                    F.Id("t"), Le, Sp, D(1), Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp,
                    F.Id("p"), Underscore, Grp(D(1)), Open, F.Id("i"), Close,
                    Sp, Land, Sp, D(0), Le, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Open, F.Id("i"), Close,
                    Sp, Land, Sp, D(0), Le, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Open, F.Id("i"), Close,
                    Sp, Land, Sp, D(0), Le, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Open, F.Id("i"), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("t"), Sp, F.Id("p"), Underscore, Grp(D(1)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("t"), Sp, F.Id("q"), Underscore, Grp(D(1)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Close, Le, Sp, RowBreak,
                    F.Id("t"), Sp, F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Underscore, Grp(D(1)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Close, Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("H"), Caret, Grp(D(2)), Open,
                    F.Id("p"), Underscore, Grp(D(2)), Comma, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Applying the scalar lemma at each coordinate and summing proves joint " +
                        "convexity of squared Hellinger distance for arbitrary finite " +
                        "pointwise-nonnegative mass functions. Neither endpoint pair is required " +
                        "to have unit total mass, and neither pair is subject to a support " +
                        "condition. The proof uses pointwise nonnegativity only when invoking the " +
                        "scalar square-root result.")),
                    Paragraph(Text(
                        "Neither convexity inequality is secretly an equality. On Unit with " +
                        "t = 1/2, take (p1,q1) = (1,0) and (p2,q2) = (0,1). The endpoint pairs " +
                        "are opposite, while both mixtures equal the constant one half; hence the " +
                        "mixture distance is zero. The weighted endpoint distance is one half for " +
                        "total variation and one for squared Hellinger distance. In this witness, " +
                        "mixing destroys all separation.")),
                    Paragraph(Text(
                        "These strict witnesses are compiled in the formal module. For each full " +
                        "joint-convexity statement, the additional checks that neither rfl nor " +
                        "simp closes the goal are themselves compiled fail_if_success " +
                        "obligations, rather than informal reports about tactic behavior.")),
                    Paragraph(Text(
                        "No strict-convexity theorem or characterization of the equality cases is " +
                        "claimed. The module does not separately state convexity in one argument " +
                        "with the other fixed, and it provides no measure-theoretic analogue. It " +
                        "also introduces no normalization assumptions beyond those absent from " +
                        "the displayed declarations.")))))));
}
