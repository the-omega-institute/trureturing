using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class LogSumEqualityDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/DivergenceSupport/LogSumEquality.";

    private static Formula At(Formula family, Formula index) => F.Seq(
        family, F.Open, index, F.Close);

    private static Formula FiniteSum(Formula index, Formula summand) => F.Seq(
        F.Sum, F.Sp, F.Underscore, F.Grp(index), F.Sp, summand);

    private static Formula Ratio(Formula numerator, Formula denominator) => F.Seq(
        F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula RatioAt(Formula numerator, Formula denominator, Formula index) =>
        Ratio(At(numerator, index), At(denominator, index));

    private static Formula LogSumEquality(
        Formula numerator,
        Formula denominator,
        Formula index) => F.Seq(
            F.Open, FiniteSum(index, At(numerator, index)), F.Close,
            F.Sp, F.Log, F.Sp, F.Open,
            Ratio(
                FiniteSum(index, At(numerator, index)),
                FiniteSum(index, At(denominator, index))),
            F.Close, F.Sp, F.Eq, F.Sp,
            FiniteSum(index, F.Seq(
                At(numerator, index), F.Sp, F.Log, F.Sp,
                F.Open, RatioAt(numerator, denominator, index), F.Close)));

    private static Formula FamilyBinders(Formula numerator, Formula denominator) => F.Seq(
        numerator, F.Comma, F.Sp, denominator, F.Colon, F.Sp,
        F.Iota, F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")));

    private static Formula NonnegativeSupportAssumptions(
        Formula numerator,
        Formula denominator,
        Formula index) => F.Seq(
            F.Open,
            F.Forall, F.Sp, index, F.Comma, F.Sp,
            F.D(0), F.Sp, F.Le, F.Sp, At(numerator, index),
            F.Close, F.Sp, F.Land, F.RowBreak,
            F.Open,
            F.Forall, F.Sp, index, F.Comma, F.Sp,
            F.D(0), F.Sp, F.Le, F.Sp, At(denominator, index),
            F.Close, F.Sp, F.Land, F.RowBreak,
            F.Open,
            F.Forall, F.Sp, index, F.Comma, F.Sp,
            At(denominator, index), F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Rightarrow, F.Sp,
            At(numerator, index), F.Sp, F.Eq, F.Sp, F.D(0),
            F.Close);

    private static Formula RatioAgreement(
        Formula numerator,
        Formula denominator,
        Formula firstIndex,
        Formula secondIndex) => F.Seq(
            F.Forall, F.Sp, firstIndex, F.Sp, secondIndex, F.Comma, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, At(denominator, firstIndex),
            F.Sp, F.Rightarrow, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, At(denominator, secondIndex),
            F.Sp, F.Rightarrow, F.Sp,
            RatioAt(numerator, denominator, firstIndex),
            F.Sp, F.Eq, F.Sp,
            RatioAt(numerator, denominator, secondIndex));

    private static Formula Statement(
        Formula binders,
        Formula premise,
        Formula conclusion) => F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, F.Iota, F.Esc,
            F.OpenBracket,
            F.Operatorname, F.Grp(F.Id("Fintype")), F.Open, F.Iota, F.Close,
            F.CloseBracket, F.Comma, F.RowBreak,
            F.Forall, F.Sp, binders, F.Comma, F.RowBreak,
            premise, F.Sp, F.Rightarrow, F.RowBreak,
            conclusion, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality in the finite log-sum inequality is characterized by proportionality on the positive reference support.",
        H("Equality in the Finite Log-Sum Inequality"),
        Blocks(
            Paragraph(Text(
                "The frozen LogSumInequality module proves the log-sum inequality under "
                + "discrete absolute continuity, exhibits a counterexample showing that the "
                + "claim is false without that condition, and gives an explicit strict "
                + "instance. It does not characterize equality. The three declarations below "
                + "complete that account by proving attainment from proportionality, extracting "
                + "common ratios from equality, and combining the two directions into a "
                + "biconditional.")),
            Paragraph(Text(
                "The proportionality hypothesis is deliberately written as a i = c * b i for "
                + "an explicit constant c. It requires no sign hypotheses and is immediately "
                + "usable downstream. Under the repository's totalization x / 0 = 0 and log 0 "
                + "= 0, both sides reduce directly to (c log c) * SUM b, including "
                + "the all-zero boundary. A pairwise-ratio formulation would require additional "
                + "support bookkeeping before downstream results could recover this global form.")),
            Paragraph(Text(
                "The converse is stated only on the positive support of b, and this is the honest "
                + "strength of the result rather than a weakness. Where the reference mass "
                + "vanishes, totalized division assigns the ratio zero and the ratio carries no "
                + "information about proportionality. Equality therefore forces agreement of "
                + "a(i) / b(i) precisely between coordinates at which b is positive.")),
            Paragraph(Text(
                "The converse rests on strict convexity. The frozen inequality uses the "
                + "non-strict Jensen bound convexOn_klFun.map_sum_le, whereas its equality case "
                + "uses InformationTheory.strictConvexOn_klFun together with "
                + "StrictConvexOn.map_sum_eq_iff_of_nonneg. Thus the inequality and its equality "
                + "case rest on different halves of the same convexity fact.")),
            Paragraph(Text(
                "All three displays are authored legally because the current statement projector "
                + "has no pinned projectable fixture for these declarations. Document "
                + "construction therefore records a ProjectionGap for each theorem.")),
            Describe.Lean(
                DescribeId.Create("proportional-families-attain-log-sum-equality"),
                DeclarationHandle.Create(LeanPrefix + "log_sum_eq_of_proportional"),
                H("Proportional families attain log-sum equality"),
                StatementSource.FromAuthor(Statement(
                    F.Seq(
                        FamilyBinders(F.Id("a"), F.Id("b")), F.Comma, F.Sp,
                        F.Id("c"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("R"))),
                    F.Seq(
                        F.Forall, F.Sp, F.Id("i"), F.Comma, F.Sp,
                        At(F.Id("a"), F.Id("i")), F.Sp, F.Eq, F.Sp,
                        F.Id("c"), F.Sp, F.Cdot, F.Sp, At(F.Id("b"), F.Id("i"))),
                    LogSumEquality(F.Id("a"), F.Id("b"), F.Id("i")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "No nonnegativity or absolute-continuity hypothesis is needed. At a coordinate "
                    + "where b vanishes, proportionality makes a vanish and totalization makes the "
                    + "summand zero. Elsewhere the quotient is c. The same division into zero and "
                    + "nonzero cases applies to the total reference mass, so both sides equal "
                    + "(c log c) times the total mass of b even when that total is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-sum-equality-forces-common-positive-support-ratios"),
                DeclarationHandle.Create(LeanPrefix + "ratios_eq_of_log_sum_eq"),
                H("Log-sum equality forces common positive-support ratios"),
                StatementSource.FromAuthor(Statement(
                    FamilyBinders(F.Id("a"), F.Id("b")),
                    NonnegativeSupportAssumptions(F.Id("a"), F.Id("b"), F.Id("i")),
                    F.Seq(
                        F.Open, LogSumEquality(F.Id("a"), F.Id("b"), F.Id("i")), F.Close,
                        F.Sp, F.Rightarrow, F.RowBreak,
                        RatioAgreement(
                            F.Id("a"), F.Id("b"), F.Id("j"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume nonnegativity and discrete absolute continuity. If the total mass of b "
                    + "vanishes, positive-support coordinates do not exist and the conclusion is "
                    + "vacuous. Otherwise the normalized b-masses are nonnegative weights summing "
                    + "to one. Rewriting log-sum equality as equality in Jensen's inequality for "
                    + "klFun and applying its strict-convexity equality criterion forces all "
                    + "ratios carrying positive weight to coincide."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-sum-equality-is-equivalent-to-common-positive-support-ratios"),
                DeclarationHandle.Create(LeanPrefix + "log_sum_eq_iff_ratios_eq"),
                H("Log-sum equality is equivalent to common positive-support ratios"),
                StatementSource.FromAuthor(Statement(
                    FamilyBinders(F.Id("a"), F.Id("b")),
                    NonnegativeSupportAssumptions(F.Id("a"), F.Id("b"), F.Id("i")),
                    F.Seq(
                        F.Open, LogSumEquality(F.Id("a"), F.Id("b"), F.Id("i")), F.Close,
                        F.Sp, F.Leftrightarrow, F.RowBreak,
                        RatioAgreement(
                            F.Id("a"), F.Id("b"), F.Id("j"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward implication is the strict-convexity result above. For the reverse "
                    + "implication, a positive coordinate of b supplies the explicit common ratio "
                    + "when the total reference mass is positive; discrete absolute continuity "
                    + "extends the resulting proportionality across zero-reference coordinates. "
                    + "When the total reference mass is zero, both families vanish and the "
                    + "proportionality theorem applies with c = 0. The biconditional therefore "
                    + "includes the all-zero boundary without adding a separate exception."))),
                DescribeRole.Theorem)
        )));
}
