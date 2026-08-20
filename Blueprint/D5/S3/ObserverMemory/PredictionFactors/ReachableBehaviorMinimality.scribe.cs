using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class ReachableBehaviorMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reachable future-behavior quotient is the canonical smallest finite realization.",
        H("Reachable Behavior Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reachable-behavior-quotient-is-canonically-minimal"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality."
                        + "finite_state_minimality"),
                H("The reachable behavior quotient is canonically minimal"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a be the actual anchor for a monoid action on X, with public "
                            + "readout O. The carrier Zbeta is constructed by restricting to "
                            + "states m acting on a and quotienting two such states when every "
                            + "continuation k gives the same public readout.")),
                    Paragraph(Text(
                        "Let Xprime be a finite competing carrier whose every state is reachable "
                            + "from its anchor and whose anchor readout agrees with the actual "
                            + "system after every action. There is a unique surjection from "
                            + "Xprime onto Zbeta sending each competing orbit point to the class "
                            + "of the corresponding actual orbit point.")),
                    Paragraph(Text(
                        "The factor chooses an action reaching each competing state. Equal "
                            + "competing orbit points have equal readouts after every continuation, "
                            + "so their actual orbit points define the same behavior class. "
                            + "Pinned Mathlib's Nat.card_le_card_of_surjective then gives the "
                            + "finite-state lower bound directly.")),
                    Paragraph(Text(
                        "The repository's controlled behavior universal property is close but "
                            + "assumes a supplied surjective realization and commuting structure; "
                            + "it does not derive the anchor-relative factor from this theorem's "
                            + "source hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula Typeclass1(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Typeclass2(string name, Formula first, Formula second) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, first, Comma, Sp,
            second, Close, CloseBracket);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula MinimalityFormula()
    {
        Formula actionType = F.Id("M");
        Formula stateType = F.Id("X");
        Formula candidateType = F.Id("Xprime");
        Formula outputType = F.Id("B");
        Formula anchor = F.Id("a");
        Formula candidateAnchor = F.Id("ap");
        Formula readout = F.Id("O");
        Formula candidateReadout = F.Id("Op");
        Formula quotient = F.Id("Zbeta");
        Formula factor = F.Id("h");
        Formula action = F.Id("m");
        Formula continuation = F.Id("k");
        Formula state = F.Id("x");
        Formula candidateState = F.Id("xp");
        Formula otherState = F.Id("y");
        Formula actualOrbit = Seq(action, Sp, Cdot, Sp, anchor);
        Formula candidateOrbit = Seq(action, Sp, Cdot, Sp, candidateAnchor);
        Formula reachable = Seq(OpenBrace, actualOrbit, Sp, Mid, Sp,
            action, Sp, InMacro, Sp, actionType, CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp,
            candidateType, Comma, Sp, outputType, Comma, RowBreak,
            Grp(), Typeclass1("Monoid", actionType), Comma, Sp,
            Typeclass2("MulAction", actionType, stateType), Comma, Sp,
            Typeclass2("MulAction", actionType, candidateType), Comma, RowBreak,
            Grp(), Typeclass1("Finite", stateType), Comma, Sp,
            Typeclass1("Finite", candidateType), Comma, RowBreak,
            Typed("a", stateType), Comma, Sp, Typed("ap", candidateType), Comma, Sp,
            Typed("O", new Formula.TypeArrow(stateType, outputType)), Comma, Sp,
            Typed("Op", new Formula.TypeArrow(candidateType, outputType)), Comma, RowBreak,
            quotient, Sp, Eq, Sp, reachable, Sp, Slash, Sp,
            Open, Forall, Sp, continuation, Comma, Sp,
            Apply(readout, Seq(continuation, Sp, Cdot, Sp, state)), Sp, Eq, Sp,
            Apply(readout, Seq(continuation, Sp, Cdot, Sp, otherState)), Close,
            Comma, RowBreak,
            Open, Forall, Sp, candidateState, Comma, Sp,
            Exists, Sp, action, Comma, Sp, candidateOrbit, Sp, Eq, Sp, candidateState,
            Close, Sp, Land, Sp,
            Open, Forall, Sp, action, Comma, Sp,
            Apply(candidateReadout, candidateOrbit), Sp, Eq, Sp,
            Apply(readout, actualOrbit), Close, RowBreak,
            Rightarrow, Sp,
            Operatorname, Grp(F.Id("card")), Open, quotient, Close, Sp, Leq, Sp,
            Operatorname, Grp(F.Id("card")), Open, candidateType, Close, Sp, Land, RowBreak,
            Exists, Bang, Sp, factor, Colon, Sp, candidateType, Sp, To, Sp, quotient,
            Comma, Sp, Call("Surjective", factor), Sp, Land, Sp,
            Open, Forall, Sp, action, Comma, Sp,
            Apply(factor, candidateOrbit), Sp, Eq, Sp,
            OpenBracket, actualOrbit, CloseBracket, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
