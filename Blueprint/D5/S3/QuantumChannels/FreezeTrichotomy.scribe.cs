using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class FreezeTrichotomyDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/QuantumChannels/FreezeTrichotomy.";

    private static Formula EntropyTax() => F.Seq(F.Delta, F.Sp, F.Id("S"));

    private static Formula PassiveEnergy() => F.Seq(
        F.Delta, F.Sp, F.Id("E"), F.Underscore, F.Grp(F.Id("pass")));

    private static Formula BetaSubscript(bool second) => F.Seq(
        F.Beta, F.Underscore, F.Grp(second ? F.D(2) : F.D(1)));

    private static Formula FreezeDeposit(Formula beta) => F.Seq(
        F.Operatorname, F.Grp(F.Id("freezeDeposit")), F.Open,
        beta, F.Comma, EntropyTax(), F.Comma, PassiveEnergy(), F.Close);

    private static Formula CriticalInverseTemperature() => F.Seq(
        F.Operatorname, F.Grp(F.Id("criticalInverseTemperature")), F.Open,
        EntropyTax(), F.Comma, PassiveEnergy(), F.Close);

    private static Formula Display(Formula formula) => F.Disp(formula);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The freeze deposit obeys the complete critical inverse-temperature sign trichotomy.",
        H("Freeze-Deposit Trichotomy and Bounds"),
        Blocks(
            Paragraph(Text(
                "The frozen module established only one branch: the freeze deposit is strictly "
                + "positive exactly when beta exceeds the critical inverse temperature. The "
                + "equality and negativity branches were absent. The first two results below "
                + "supply those branches, so the three parallel criteria are exhaustive and the "
                + "one-sided test becomes a sign trichotomy.")),
            Paragraph(Text(
                "No combined trichotomy theorem is added. This is a deliberate decision rather "
                + "than an omission: the three parallel criterion names already display the "
                + "trichotomy, and a fourth declaration would merely restate proved content under "
                + "a new name.")),
            Paragraph(Text(
                "The two quantitative conclusions have different side hypotheses, and neither is "
                + "decorative. Strict monotonicity requires a strictly positive entropy tax. With "
                + "a zero tax the deposit is constant in beta, whereas with a negative tax it "
                + "decreases. The upper bound requires only a nonnegative entropy tax together "
                + "with positive beta; it does not require the tax to be strictly positive.")),
            Paragraph(Text(
                "The upper bound is finite: the freeze deposit is at most the passive-energy "
                + "shift. No limiting statement is claimed. In particular, this module does not "
                + "prove that the deposit converges to the passive-energy shift as beta grows.")),
            Paragraph(Text(
                "All four displays are authored legally because the current statement projector "
                + "has no pinned projectable fixture for these declarations. Document construction "
                + "therefore records a ProjectionGap for each theorem.")),
            Describe.Lean(
                DescribeId.Create("the-freeze-deposit-vanishes-exactly-at-critical-temperature"),
                DeclarationHandle.Create(
                    LeanPrefix + "decoherence_freeze_eq_zero_iff_at_critical"),
                H("The freeze deposit vanishes exactly at the critical inverse temperature"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.D(0), F.Lt, F.Beta, F.Sp, F.Land, F.Sp,
                    F.D(0), F.Lt, PassiveEnergy(), F.Sp, F.Rightarrow, F.Sp, F.Open,
                    FreezeDeposit(F.Beta), F.Sp, F.Eq, F.Sp, F.D(0),
                    F.Sp, F.Leftrightarrow, F.Sp,
                    F.Beta, F.Sp, F.Eq, F.Sp, CriticalInverseTemperature(), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive beta and a positive passive-energy shift, the deposit vanishes "
                    + "precisely when beta equals the entropy-tax to passive-energy ratio. The two "
                    + "positivity assumptions justify both divisions used to pass between the "
                    + "zero-deposit equation and the critical-temperature equation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-freeze-deposit-is-negative-exactly-below-critical-temperature"),
                DeclarationHandle.Create(
                    LeanPrefix + "decoherence_freeze_neg_iff_below_critical"),
                H("The freeze deposit is negative exactly below the critical inverse temperature"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.D(0), F.Lt, F.Beta, F.Sp, F.Land, F.Sp,
                    F.D(0), F.Lt, PassiveEnergy(), F.Sp, F.Rightarrow, F.Sp, F.Open,
                    FreezeDeposit(F.Beta), F.Sp, F.Lt, F.Sp, F.D(0),
                    F.Sp, F.Leftrightarrow, F.Sp,
                    F.Beta, F.Sp, F.Lt, F.Sp, CriticalInverseTemperature(), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same positivity assumptions, a negative deposit is equivalent to "
                    + "beta lying below the critical inverse temperature. Together with equality "
                    + "here and positivity in the frozen module, this completes the three possible "
                    + "signs without introducing a duplicate wrapper theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-positive-entropy-tax-makes-the-freeze-deposit-strictly-increase"),
                DeclarationHandle.Create(LeanPrefix + "freeze_deposit_strictly_increases"),
                H("A positive entropy tax makes the freeze deposit strictly increase"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.D(0), F.Lt, BetaSubscript(false), F.Sp, F.Land, F.Sp,
                    BetaSubscript(false), F.Sp, F.Lt, F.Sp, BetaSubscript(true),
                    F.Sp, F.Land, F.Sp, F.D(0), F.Lt, EntropyTax(),
                    F.Sp, F.Rightarrow, F.Sp,
                    FreezeDeposit(BetaSubscript(false)), F.Sp, F.Lt, F.Sp,
                    FreezeDeposit(BetaSubscript(true))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If beta one is positive, beta two is larger, and the entropy tax is strictly "
                    + "positive, then the tax divided by beta strictly decreases. Subtracting that "
                    + "quantity from the same passive-energy shift makes the freeze deposit "
                    + "strictly increase. A zero or negative tax would invalidate this strict "
                    + "conclusion in exactly the ways stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-freeze-deposit-is-bounded-by-the-passive-energy-shift"),
                DeclarationHandle.Create(LeanPrefix + "freeze_deposit_le_passive_energy"),
                H("The freeze deposit is bounded by the passive-energy shift"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.D(0), F.Lt, F.Beta, F.Sp, F.Land, F.Sp,
                    F.D(0), F.Leq, EntropyTax(), F.Sp, F.Rightarrow, F.Sp,
                    FreezeDeposit(F.Beta), F.Sp, F.Leq, F.Sp, PassiveEnergy()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive beta, a nonnegative entropy tax yields a nonnegative scaled tax. "
                    + "Subtracting it from the passive-energy shift proves the finite upper bound. "
                    + "The theorem makes no assertion that this bound is approached or attained "
                    + "as beta tends toward any limit."))),
                DescribeRole.Theorem)
        )));
}
