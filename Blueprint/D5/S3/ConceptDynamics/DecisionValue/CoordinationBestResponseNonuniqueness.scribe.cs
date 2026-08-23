using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class CoordinationBestResponseNonuniquenessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two coordination equilibria refute unique selection by local best responses.",
        H("Coordination Best-Response Nonuniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-best-responses-do-not-select-unique-outcome"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/"
                        + "CoordinationBestResponseNonuniqueness."
                        + "local_best_responses_do_not_select_unique_outcome"),
                H("Local best responses do not select a unique social outcome"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are exactly two players and two Boolean actions. Each player's "
                            + "utility is one when the two actions agree and zero when they "
                            + "differ, exactly as specified by the public payoff hypothesis.")),
                    Paragraph(Text(
                        "A profile is locally stable when changing either one player's action "
                            + "cannot increase that player's utility. This unilateral comparison "
                            + "is constructed directly in the public statement rather than hidden "
                            + "behind a new equilibrium definition.")),
                    Paragraph(Text(
                        "At the all-zero profile and at the all-one profile, the current payoff "
                            + "is one and every deviation yields either zero or one. Both profiles "
                            + "therefore consist of best responses. Since the two profiles differ, "
                            + "there cannot be a unique locally stable collective action.")),
                    Paragraph(Text(
                        "Repository search found a related threshold-public-good theorem, but its "
                            + "utility is different and cannot be reused here. Pinned Mathlib has "
                            + "no exact game-theory theorem for this claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula player = F.Id("i");
        Formula profile = F.Id("a");
        Formula alternative = F.Id("b");
        Formula utility = F.Id("u");
        Formula stable = Call("Stable", utility, profile);
        Formula players = Call("Fin", D(2));
        Formula actions = Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace);
        Formula profileType = Seq(players, Sp, To, Sp, actions);
        Formula utilityType = Seq(
            players, Sp, To, Sp, Open, profileType, Close, Sp, To, Sp,
            Mathbb, Grp(F.Id("N")));
        Formula updated = Call("update", profile, player, alternative);
        Formula stableDefinition = Seq(
            Forall, Sp, profile, Colon, Sp, profileType, Comma, Sp,
            stable, Colon, Eq, Sp,
            Forall, Sp, player, Sp, InMacro, Sp, players, Comma, Sp,
            alternative, Sp, InMacro, Sp, actions, Comma, Sp,
            Call("u", player, updated), Sp, Leq, Sp,
            Call("u", player, profile));
        Formula payoff = Seq(
            Forall, Sp, player, Sp, InMacro, Sp, players, Comma, Sp,
            profile, Colon, Sp, profileType, Comma, Sp,
            Call("u", player, profile), Sp, Eq, Sp,
            Call("ifEqualThenOneElseZero",
                Subscript(profile, D(0)), Subscript(profile, D(1))));
        Formula zeroProfile = Seq(D(0), Caret, D(2));
        Formula oneProfile = Seq(D(1), Caret, D(2));
        Formula unique = Seq(
            Exists, Bang, Sp, profile, Colon, Sp, profileType, Comma, Sp,
            Call("Stable", utility, profile));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, utility, Colon, Sp, utilityType, Comma,
            RowBreak, Grp(),
            stableDefinition, Comma, RowBreak, Grp(),
            Open, payoff, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("Stable", utility, zeroProfile), Sp, Land, Sp,
            Call("Stable", utility, oneProfile), Sp, Land, RowBreak, Grp(),
            Neg, Sp, unique, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
