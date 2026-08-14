using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class LandauerSaturationDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/DivergenceSupport/LandauerSaturation.";

    private static Formula HeatTerm() => F.Seq(
        F.Id("beta"), F.Sp, F.Cdot, F.Sp, F.Id("heat"));

    private static Formula NegativeEntropyChange() => F.Seq(
        F.Minus, F.Id("entropyChange"));

    private static Formula RemainderSum() => F.Seq(
        F.Id("mutualInfo"), F.Sp, F.Plus, F.Sp, F.Id("divergence"));

    private static Formula Equality(Formula left, Formula right) => F.Seq(
        left, F.Sp, F.Eq, F.Sp, right);

    private static Formula Balance() => Equality(
        HeatTerm(),
        F.Seq(NegativeEntropyChange(), F.Sp, F.Plus, F.Sp, RemainderSum()));

    private static Formula Assumptions(bool includeNonnegativity) =>
        includeNonnegativity
            ? F.Seq(
                Balance(), F.Sp, F.Land, F.Sp,
                F.D(0), F.Sp, F.Le, F.Sp, F.Id("mutualInfo"), F.Sp, F.Land, F.Sp,
                F.D(0), F.Sp, F.Le, F.Sp, F.Id("divergence"))
            : Balance();

    private static Formula Statement(Formula conclusion, bool includeNonnegativity) =>
        F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp,
            F.Id("beta"), F.Comma, F.Sp,
            F.Id("heat"), F.Comma, F.Sp,
            F.Id("entropyChange"), F.Comma, F.Sp,
            F.Id("mutualInfo"), F.Comma, F.Sp,
            F.Id("divergence"), F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            Assumptions(includeNonnegativity), F.Sp, F.Rightarrow, F.RowBreak,
            conclusion, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Landauer slack separates equality from strictness through its two nonnegative remainders.",
        H("Saturation and Strictness of the Landauer Bound"),
        Blocks(
            Paragraph(Text(
                "The frozen LandauerBound module obtains its inequality by discarding the "
                + "nonnegative mutual-information and divergence remainders, but it does not say "
                + "when equality holds. The slack identity below supplies exactly that missing "
                + "information: the gap in the bound is the sum of the two discarded remainders. "
                + "Every subsequent criterion is a consequence of this identity.")),
            Paragraph(Text(
                "The conjunctive saturation criterion is the primary form. It identifies each "
                + "discarded remainder separately, so saturation is read as no residual mutual "
                + "information and no reservoir divergence, rather than merely as vanishing of "
                + "their sum. The sum criterion is also stated and requires only the balance, "
                + "without either nonnegativity hypothesis. Passing from a zero sum to the two "
                + "separate zero statements is exactly where both nonnegativity hypotheses enter.")),
            Paragraph(Text(
                "Under the same nonnegativity hypotheses as the frozen inequality, equality and "
                + "strict inequality are exhaustive. The conjunctive theorem characterizes the "
                + "equality case, while the final theorem characterizes the strict case by "
                + "positivity of the total discarded remainder.")),
            Paragraph(Text(
                "Physically, saturation is read here as no residual mutual information and no "
                + "reservoir divergence. That reading is deliberately limited: this module proves "
                + "only consequences of a real-number balance. It does not model a physical "
                + "process, derive the balance from any dynamics, or establish that the variables "
                + "named mutualInfo and divergence are the physical quantities their names suggest.")),
            Paragraph(Text(
                "All four displays are authored legally because the current statement projector "
                + "has no pinned projectable fixture for these declarations. Document construction "
                + "therefore records a ProjectionGap for each theorem.")),
            Describe.Lean(
                DescribeId.Create("landauer-slack-is-the-sum-of-discarded-remainders"),
                DeclarationHandle.Create(LeanPrefix + "landauer_slack_of_balance"),
                H("The Landauer slack is the sum of the discarded remainders"),
                StatementSource.FromAuthor(Statement(F.Seq(
                    HeatTerm(), F.Sp, F.Minus, F.Sp,
                    F.Open, NegativeEntropyChange(), F.Close,
                    F.Sp, F.Eq, F.Sp, RemainderSum()), false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Rearranging the exact balance identifies the slack without an inequality or "
                    + "a sign assumption. Thus the quantity discarded in the frozen lower-bound "
                    + "argument is not merely bounded by the two remainders; it is exactly their sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("landauer-saturation-is-vanishing-of-the-remainder-sum"),
                DeclarationHandle.Create(LeanPrefix + "landauer_saturation_sum_iff"),
                H("Saturation is equivalent to a zero remainder sum"),
                StatementSource.FromAuthor(Statement(F.Seq(
                    Equality(NegativeEntropyChange(), HeatTerm()),
                    F.Sp, F.Leftrightarrow, F.Sp,
                    Equality(RemainderSum(), F.D(0))), false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The slack vanishes exactly when the sum of mutualInfo and divergence vanishes. "
                    + "Only the balance is used. Without nonnegativity, cancellation between the "
                    + "two real remainders is possible, so this algebraic criterion alone does not "
                    + "identify either remainder separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("landauer-saturation-is-separate-vanishing-of-both-remainders"),
                DeclarationHandle.Create(LeanPrefix + "landauer_saturation_iff"),
                H("Saturation means that both discarded remainders vanish"),
                StatementSource.FromAuthor(Statement(F.Seq(
                    Equality(NegativeEntropyChange(), HeatTerm()),
                    F.Sp, F.Leftrightarrow, F.Sp, F.Open,
                    Equality(F.Id("mutualInfo"), F.D(0)),
                    F.Sp, F.Land, F.Sp,
                    Equality(F.Id("divergence"), F.D(0)), F.Close), true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the primary saturation criterion. Nonnegativity prevents cancellation, "
                    + "so a zero total remainder is equivalent to mutualInfo being zero and "
                    + "divergence being zero. It therefore exposes the two independent equality "
                    + "conditions hidden by the frozen act of discarding their sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("landauer-strictness-is-positivity-of-the-remainder-sum"),
                DeclarationHandle.Create(LeanPrefix + "landauer_strict_iff"),
                H("Strictness is equivalent to a positive remainder sum"),
                StatementSource.FromAuthor(Statement(F.Seq(
                    NegativeEntropyChange(), F.Sp, F.Lt, F.Sp, HeatTerm(),
                    F.Sp, F.Leftrightarrow, F.Sp,
                    F.D(0), F.Sp, F.Lt, F.Sp, RemainderSum()), true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the two nonnegativity hypotheses, the frozen lower bound rules out the "
                    + "opposite order. Its inequality is strict exactly when the exact slack is "
                    + "positive, equivalently when the sum of the discarded remainders is positive. "
                    + "Together with the preceding saturation criterion, this exhausts the bound's "
                    + "equality and strict cases."))),
                DescribeRole.Theorem)
        )));
}
