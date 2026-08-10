using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class LogSumInequalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/DivergenceSupport/LogSumInequality",
            "The finite log-sum inequality and joint convexity of real-valued KL divergence under discrete absolute continuity."),
        H("Log-Sum Inequality and Joint Convexity on General Support"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-log-sum-under-discrete-absolute-continuity"),
                H("Coordinatewise relative entropy dominates its aggregate"),
                LeanTheorem(
                    "D5/S3/DivergenceSupport/LogSumInequality.log_sum_inequality"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("a"), Comma, Sp, F.Id("b"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("a"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("b"), Open, F.Id("i"), Close, Close,
                    Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("b"), Open, F.Id("i"), Close, Eq, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("a"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("a"), Open, F.Id("i"), Close, Close, Sp,
                    Log, Sp, Open,
                    Frac,
                    Grp(
                        Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                        F.Id("a"), Open, F.Id("i"), Close),
                    Grp(
                        Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                        F.Id("b"), Open, F.Id("i"), Close),
                    Close, Le, Sp, RowBreak,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("a"), Open, F.Id("i"), Close, Sp,
                    Log, Sp, Open,
                    Frac,
                    Grp(F.Id("a"), Open, F.Id("i"), Close),
                    Grp(F.Id("b"), Open, F.Id("i"), Close),
                    Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let a and b be nonnegative mass vectors on a finite type, with discrete " +
                        "absolute continuity: b(i) = 0 implies a(i) = 0. The theorem says that " +
                        "aggregating the two vectors before comparing them can only understate " +
                        "their relative entropy. The sum of the coordinatewise comparisons " +
                        "dominates the comparison of the total masses. This scalar inequality " +
                        "is the engine behind the convexity and data-processing consequences of " +
                        "finite classical divergence.")),
                    Paragraph(Text(
                        "The absolute-continuity hypothesis is indispensable: without it, the " +
                        "inequality is false, not merely unproved or vacuous. On Bool, take " +
                        "a(i) = 1 at both coordinates and take b(false) = 1, b(true) = 0. The " +
                        "left side aggregates to 2 log 2, which is strictly positive. The right " +
                        "side is zero: the nonzero-denominator coordinate contributes log 1 = 0, " +
                        "while Lean's conventions x / 0 = 0 and Real.log 0 = 0 make the other " +
                        "coordinate contribute 1 log 0 = 0 rather than the positive infinity it " +
                        "carries in extended-real relative entropy. Thus the unguarded statement " +
                        "asserts 2 log 2 <= 0. This counterexample was compiled by the author in " +
                        "the formal module and compiled independently by the caller.")),
                    Paragraph(Text(
                        "The value assigned at a zero-denominator coordinate is therefore a Lean " +
                        "convention, not a mathematical claim that the corresponding relative " +
                        "entropy is finite or zero. Any theorem ranging over such coordinates " +
                        "must retain b(i) = 0 implies a(i) = 0 if its divergence terminology is " +
                        "to have the intended mathematical meaning. Strict positivity of b is " +
                        "not required. The support condition suffices, and together with " +
                        "nonnegativity it makes a zero total mass for b force a zero total mass " +
                        "for a.")),
                    Paragraph(Text(
                        "When the total mass of b is positive, the proof normalizes b, applies " +
                        "finite Jensen convexity to InformationTheory.klFun, and cancels the " +
                        "affine correction in klFun to obtain the displayed logarithmic terms. " +
                        "The zero-total branch is discharged by the support condition. No " +
                        "normalization of either mass vector is assumed.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("kl-divergence-is-jointly-convex-on-general-support"),
                H("Finite KL divergence is jointly convex on general support"),
                LeanTheorem(
                    "D5/S3/DivergenceSupport/LogSumInequality.kl_divergence_joint_convex"),
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
                    Open, Open,
                    D(0), Le, Sp, F.Id("t"), Sp, Land, Sp,
                    F.Id("t"), Le, Sp, D(1), Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp,
                    F.Id("p"), Underscore, Grp(D(1)), Open, F.Id("i"), Close,
                    Sp, Land, Sp,
                    D(0), Le, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Open, F.Id("i"), Close,
                    Sp, Land, Sp,
                    D(0), Le, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Open, F.Id("i"), Close,
                    Sp, Land, Sp,
                    D(0), Le, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Open, F.Id("i"), Close,
                    Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    Open,
                    F.Id("q"), Underscore, Grp(D(1)), Open, F.Id("i"), Close,
                    Eq, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Underscore, Grp(D(1)), Open, F.Id("i"), Close,
                    Eq, D(0), Close, Sp, Land, Sp,
                    Open,
                    F.Id("q"), Underscore, Grp(D(2)), Open, F.Id("i"), Close,
                    Eq, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Underscore, Grp(D(2)), Open, F.Id("i"), Close,
                    Eq, D(0), Close, Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    F.Id("t"), Sp, F.Id("p"), Underscore, Grp(D(1)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("p"), Underscore, Grp(D(2)),
                    Vert, Sp,
                    F.Id("t"), Sp, F.Id("q"), Underscore, Grp(D(1)), Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Close, Le, Sp, RowBreak,
                    F.Id("t"), Sp,
                    F.Id("D"), Open,
                    F.Id("p"), Underscore, Grp(D(1)), Vert, Sp,
                    F.Id("q"), Underscore, Grp(D(1)), Close, Plus,
                    Open, D(1), Minus, F.Id("t"), Close, Sp,
                    F.Id("D"), Open,
                    F.Id("p"), Underscore, Grp(D(2)), Vert, Sp,
                    F.Id("q"), Underscore, Grp(D(2)), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For each coordinate i, apply the two-term log-sum inequality on Bool " +
                        "with a = (t p1(i), (1-t) p2(i)) and b = (t q1(i), " +
                        "(1-t) q2(i)). The bounds 0 <= t <= 1 make both mixing weights " +
                        "nonnegative, while the two original support conditions supply the " +
                        "support condition for the scaled pairs, including at the endpoint " +
                        "weights. Summing the resulting scalar inequality over i gives the " +
                        "displayed joint-convexity bound.")),
                    Paragraph(Text(
                        "Beyond the two log-sum inputs' nonnegativity and absolute-continuity " +
                        "hypotheses, only the mixing range 0 <= t <= 1 is added. Probability " +
                        "normalization is not required. Joint convexity is therefore a " +
                        "coordinatewise corollary here, not an independent argument: the " +
                        "load-bearing half of the module is the log-sum inequality.")),
                    Paragraph(Text(
                        "DivergenceSupport is registered for finite classical-divergence " +
                        "identities and bounds under general-support and absolute-continuity " +
                        "conventions. This theorem lies exactly in that regime, which is why it " +
                        "belongs here rather than in the TotalVariation bucket. The module does " +
                        "not characterize equality, provide a continuous or measure-theoretic " +
                        "analogue, establish convexity for other distances, or generalize the " +
                        "claim to Renyi divergence. All logarithms are natural, so the units are " +
                        "nats.")))))));
}
