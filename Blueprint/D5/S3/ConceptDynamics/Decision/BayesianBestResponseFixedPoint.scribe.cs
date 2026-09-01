using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class BayesianBestResponseFixedPointDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Decision/BayesianBestResponseFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Bayesian best responses form a nonempty correspondence whose equilibria "
            + "are membership fixed points.",
        H("Bayesian Best Responses as Fixed Points"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-expected-utility"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "conditionalExpectedUtility"),
                H("Finite conditional expected utility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a finite state space, conditional expected utility is the prior-"
                        + "weighted utility sum over one signal fiber divided by that fiber's "
                        + "prior mass. The best-response definition invokes it only when this "
                        + "mass is strictly positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("best-responses"),
                DeclarationHandle.Create(DeclarationPrefix + "bestResponses"),
                H("The Bayesian best-response correspondence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A policy belongs to the response set when, at every positive-mass signal, "
                        + "its selected action realizes an IsGreatest value in the range of "
                        + "conditional expected utility. No condition is imposed at a zero-mass "
                        + "signal, and several maximizing actions may coexist."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-argmax-iff-unnormalized-argmax"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "conditional_argmax_iff_unnormalized_argmax"),
                H("Positive normalization preserves the full argmax set"),
                StatementSource.FromAuthor(NormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive-probability signal, every conditional utility comparison "
                        + "is equivalent to the corresponding comparison between weighted-sum "
                        + "numerators. The proof divides both candidates by the same positive "
                        + "fiber mass, so it preserves all ties rather than choosing a unique "
                        + "maximizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("best-responses-nonempty"),
                DeclarationHandle.Create(DeclarationPrefix + "bestResponses_nonempty"),
                H("Finite best-response sets are nonempty"),
                StatementSource.FromAuthor(ResponseExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite nonempty action type has a maximizing conditional utility at each "
                        + "signal. Choosing one maximizer for each signal constructs a policy in "
                        + "the response set; zero-probability signals require no additional "
                        + "obligation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("is-bayesian-nash-equilibrium"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "IsBayesianNashEquilibrium"),
                H("Two-player Bayesian Nash equilibrium"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two players with common finite state, signal, and action types, a "
                        + "profile is an equilibrium exactly when it belongs to the joint "
                        + "best-response set evaluated at itself."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bayesian-nash-equilibrium-iff-fixed-point"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "bayesian_nash_equilibrium_iff_fixed_point"),
                H("Bayesian Nash equilibrium is a best-response fixed point"),
                StatementSource.FromAuthor(BayesianFixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Unfolding the joint correspondence says that each player's policy "
                            + "belongs to its response set against the other player's policy. "
                            + "This is the source fixed-point equation in a two-player model.")),
                    Paragraph(Text(
                        "The formalization deliberately uses common signal and action types for "
                            + "the two players. It does not claim the heterogeneous general-n "
                            + "version, nor does it claim existence of a fixed point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-agent-bayesian-equilibrium-iff-fixed-point"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "single_agent_bayesian_equilibrium_iff_fixed_point"),
                H("The one-agent specialization is policy in BR of itself"),
                StatementSource.FromAuthor(SingleAgentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the response input and output policy are the same coordinate, the "
                        + "equilibrium statement has the literal membership-fixed-point form "
                        + "policy in BR(policy)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordination-false-profile-is-bayesian-nash"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "coordination_false_profile_is_bayesian_nash"),
                H("The all-false coordination profile is a BNE"),
                StatementSource.FromAuthor(CoordinationEquilibriumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the unit-state, unit-signal, two-action coordination game, both players "
                        + "receive utility one when their actions agree and zero otherwise. The "
                        + "all-false profile gives each player a maximizing action and is "
                        + "therefore a concrete Bayesian Nash equilibrium."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordination-mismatch-player-zero-strict-deviation"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "coordination_mismatch_player_zero_strict_deviation"),
                H("Player zero strictly improves at the mismatched profile"),
                StatementSource.FromAuthor(StrictDeviationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the profile where player zero chooses false and player one chooses true, "
                        + "player zero raises conditional expected utility from zero to one by "
                        + "switching to true."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordination-mismatch-not-bayesian-nash"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "coordination_mismatch_not_bayesian_nash"),
                H("The mismatched profile is not a BNE"),
                StatementSource.FromAuthor(NonEquilibriumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit strict deviation contradicts the IsGreatest upper-bound "
                        + "clause for player zero. Thus the response definition does not "
                        + "classify every strategy profile as an equilibrium."))),
                DescribeRole.Theorem))));

    private static Formula App(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula NormalizationFormula()
    {
        Formula observed = F.Id("b");
        Formula policy = F.Id("pi");
        Formula conditionalRange = App("range", Subscript(F.Id("CEU"), observed));
        Formula numeratorRange = App("range", Subscript(F.Id("Numerator"), observed));
        Formula selected = new Formula.Apply(policy, [observed]);

        return Disp(Seq(
            D(0), Sp, Lt, Sp, App("Pr", observed), Sp, Rightarrow, RowBreak, Grp(),
            App("IsGreatest", conditionalRange,
                App("CEU", observed, selected)),
            Sp, Iff, Sp,
            App("IsGreatest", numeratorRange,
                App("Numerator", observed, selected)), Dot));
    }

    private static Formula ResponseExistenceFormula()
    {
        Formula action = F.Id("A");
        Formula otherPolicy = Subscript(F.Id("pi"), Seq(Minus, F.Id("i")));
        return Disp(Seq(
            App("Finite", action), Sp, Land, Sp,
            App("Nonempty", action), Sp, Rightarrow, Sp,
            Exists, Sp, F.Id("pi"), Comma, Sp,
            F.Id("pi"), Sp, InMacro, Sp, App("BR", otherPolicy), Dot));
    }

    private static Formula BayesianFixedPointFormula()
    {
        Formula profile = F.Id("pi");
        Formula player = F.Id("i");
        Formula ownPolicy = Subscript(profile, player);
        Formula otherPolicy = Subscript(profile, Seq(Minus, player));

        return Disp(Seq(
            App("BNE", profile), Sp, Iff, Sp,
            Forall, Sp, player, Sp, InMacro, Sp, App("Fin", D(2)), Comma, Sp,
            ownPolicy, Sp, InMacro, Sp,
            App("BR", player, otherPolicy), Dot));
    }

    private static Formula SingleAgentFormula()
    {
        Formula policy = F.Id("pi");
        return Disp(Seq(
            App("SingleBNE", policy), Sp, Iff, Sp,
            policy, Sp, InMacro, Sp, App("BR", policy), Dot));
    }

    private static Formula CoordinationEquilibriumFormula() =>
        Disp(Seq(App("BNE", Subscript(F.Id("pi"), D(0))), Dot));

    private static Formula StrictDeviationFormula() =>
        Disp(Seq(
            App("CEU", D(0), F.Id("true"),
                Subscript(F.Id("pi"), D(1))),
            Sp, Gt, Sp,
            App("CEU", D(0), F.Id("false"),
                Subscript(F.Id("pi"), D(1))), Dot));

    private static Formula NonEquilibriumFormula() =>
        Disp(Seq(Neg, Sp, App("BNE", Subscript(F.Id("pi"), F.Id("mismatch"))), Dot));
}
