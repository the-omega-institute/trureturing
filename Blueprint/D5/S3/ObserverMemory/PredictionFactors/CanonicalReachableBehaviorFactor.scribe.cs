using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class CanonicalReachableBehaviorFactorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every reachable realization of the same anchor behavior maps uniquely and "
            + "surjectively to the canonical reachable behavior quotient.",
        H("Canonical Reachable Behavior Factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-reachable-behavior-factor"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor."
                        + "canonical_reachable_behavior_factor"),
                H("The reachable behavior factor is unique and surjective"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let two monoid actions have actual anchors a and a', with public "
                            + "readouts O and O'. Every competing state is required to be "
                            + "reachable from a', and the two anchor readouts agree after every "
                            + "allowed action.")),
                    Paragraph(Text(
                        "The target is the existing reachable behavior quotient: reachable "
                            + "source states are identified exactly when every continuation has "
                            + "the same public readout.")),
                    Paragraph(Text(
                        "There is a unique surjection h from the competing carrier to that "
                            + "quotient, and h sends every point m acting on a' to the behavior "
                            + "class of m acting on a. Reachability makes this computation rule "
                            + "determine h on the whole competing carrier."))),
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

    private static Formula TheoremFormula()
    {
        Formula actionType = F.Id("M");
        Formula stateType = F.Id("X");
        Formula candidateType = F.Id("Xprime");
        Formula outputType = F.Id("B");
        Formula anchor = F.Id("a");
        Formula candidateAnchor = F.Id("aprime");
        Formula readout = F.Id("O");
        Formula candidateReadout = F.Id("Oprime");
        Formula action = F.Id("m");
        Formula candidateState = F.Id("xprime");
        Formula factor = F.Id("h");
        Formula actualOrbit = Seq(action, Sp, Cdot, Sp, anchor);
        Formula candidateOrbit = Seq(action, Sp, Cdot, Sp, candidateAnchor);
        Formula quotient = Call("ReachableBehaviorQuotient", actionType, anchor, readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp,
            candidateType, Comma, Sp, outputType, Comma, RowBreak,
            Grp(), Typeclass1("Monoid", actionType), Comma, Sp,
            Typeclass2("MulAction", actionType, stateType), Comma, Sp,
            Typeclass2("MulAction", actionType, candidateType), Comma, RowBreak,
            Grp(), Typed("a", stateType), Comma, Sp,
            Typed("aprime", candidateType), Comma, Sp,
            Typed("O", new Formula.TypeArrow(stateType, outputType)), Comma, Sp,
            Typed("Oprime", new Formula.TypeArrow(candidateType, outputType)), Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, Typed("xprime", candidateType), Comma, Sp,
            Exists, Sp, Typed("m", actionType), Comma, Sp,
            candidateOrbit, Sp, Eq, Sp, candidateState, Close, Sp, Land, Sp,
            Open, Forall, Sp, Typed("m", actionType), Comma, Sp,
            Apply(candidateReadout, candidateOrbit), Sp, Eq, Sp,
            Apply(readout, actualOrbit), Close, RowBreak, Grp(),
            Rightarrow, Sp,
            Exists, Bang, Sp, factor, Colon, Sp, candidateType, Sp, To, Sp,
            quotient, Comma, Sp, Call("Surjective", factor), Sp, Land, RowBreak,
            Grp(), Open, Forall, Sp, Typed("m", actionType), Comma, Sp,
            Apply(factor, candidateOrbit), Sp, Eq, Sp,
            Call("behaviorClass", anchor, readout, action), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
