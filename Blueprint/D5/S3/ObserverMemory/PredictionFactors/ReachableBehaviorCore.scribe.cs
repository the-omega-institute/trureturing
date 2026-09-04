using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class ReachableBehaviorCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reachable future-behavior quotient is reached, separated by future protocols, "
            + "stable under protocol prefixes, and universal among reachable realizations.",
        H("Reachable Behavior Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reachable-behavior-core"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorCore."
                        + "reachable_behavior_core"),
                H("The reachable behavior quotient has all four core properties"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a monoid of allowed protocols act on a state carrier from an actual "
                            + "anchor, and let O be the public readout. The target is the existing "
                            + "quotient of reachable states by equality of every future readout.")),
                    Paragraph(Text(
                        "Every quotient class is produced by an allowed protocol. Injectivity of "
                            + "the kernel lift makes distinct classes differ at some continuation, "
                            + "and left multiplication constructs the unique update induced by "
                            + "each protocol prefix.")),
                    Paragraph(Text(
                        "For every other reachable action carrier with the same anchor behavior, "
                            + "there is a unique surjection to the quotient, determined on every "
                            + "orbit point by its canonical behavior class."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity")),
        ]));

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula Typeclass1(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Typeclass2(string name, Formula first, Formula second) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, first, Comma, Sp,
            second, Close, CloseBracket);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula protocol = F.Id("M");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula candidateType = F.Id("Xprime");
        Formula anchor = F.Id("a");
        Formula readout = F.Id("O");
        Formula candidateAnchor = F.Id("aprime");
        Formula candidateReadout = F.Id("Oprime");
        Formula first = F.Id("z1");
        Formula second = F.Id("z2");
        Formula continuation = F.Id("c");
        Formula protocolPrefix = F.Id("p");
        Formula action = F.Id("m");
        Formula candidateState = F.Id("xprime");
        Formula coreUpdate = F.Id("U");
        Formula factor = F.Id("h");
        Formula quotient = Call("ReachableBehaviorQuotient", protocol, anchor, readout);
        Formula behaviorClass = Call("behaviorClass", anchor, readout, action);
        Formula prefixedClass = Call("behaviorClass", anchor, readout,
            Seq(protocolPrefix, Sp, Cdot, Sp, action));
        Formula futureBehavior = Call("futureBehavior", anchor, readout);
        Formula firstReadout = Call("kerLift", futureBehavior, first, continuation);
        Formula secondReadout = Call("kerLift", futureBehavior, second, continuation);
        Formula candidateOrbit = Seq(action, Sp, Cdot, Sp, candidateAnchor);
        Formula sourceOrbit = Seq(action, Sp, Cdot, Sp, anchor);

        Formula reachability = Call("Surjective", Lambda(action, behaviorClass));
        Formula separation = Seq(
            Forall, Sp, Typed(first, quotient), Comma, Sp, Typed(second, quotient), Comma, Sp,
            NotEqual(first, second), Sp, Rightarrow, Sp,
            Exists, Sp, Typed(continuation, protocol), Comma, Sp,
            NotEqual(firstReadout, secondReadout));
        Formula updateStability = Seq(
            Forall, Sp, Typed(protocolPrefix, protocol), Comma, Sp,
            Exists, Bang, Sp,
            Typed(coreUpdate, new Formula.TypeArrow(quotient, quotient)), Comma, Sp,
            Forall, Sp, Typed(action, protocol), Comma, Sp,
            Call("U", behaviorClass), Sp, Eq, Sp, prefixedClass);
        Formula candidateReachability = Seq(
            Forall, Sp, Typed(candidateState, candidateType), Comma, Sp,
            Exists, Sp, Typed(action, protocol), Comma, Sp,
            candidateOrbit, Sp, Eq, Sp, candidateState);
        Formula sameBehavior = Seq(
            Forall, Sp, Typed(action, protocol), Comma, Sp,
            Call("Oprime", candidateOrbit), Sp, Eq, Sp, Call("O", sourceOrbit));
        Formula universalFactor = Seq(
            Exists, Bang, Sp,
            Typed(factor, new Formula.TypeArrow(candidateType, quotient)), Comma, Sp,
            Call("Surjective", factor), Sp, Land, Sp,
            Open, Forall, Sp, Typed(action, protocol), Comma, Sp,
            Call("h", candidateOrbit), Sp, Eq, Sp, behaviorClass, Close);
        Formula universality = Seq(
            Forall, Sp, Typed(candidateType, type), Comma, Sp,
            Typeclass2("MulAction", protocol, candidateType), Comma, Sp,
            Typed(candidateAnchor, candidateType), Comma, Sp,
            Typed(candidateReadout, new Formula.TypeArrow(candidateType, outputType)), Comma,
            RowBreak, Grp(),
            Open, candidateReachability, Close, Sp, Land, Sp,
            Open, sameBehavior, Close, Sp, Rightarrow, Sp, universalFactor);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(protocol, type), Comma, Sp,
            Typed(stateType, type), Comma, Sp, Typed(outputType, type), Comma, RowBreak, Grp(),
            Typeclass1("Monoid", protocol), Comma, Sp,
            Typeclass2("MulAction", protocol, stateType), Comma, Sp,
            Typed(anchor, stateType), Comma, Sp,
            Typed(readout, new Formula.TypeArrow(stateType, outputType)), Comma, RowBreak, Grp(),
            Open, reachability, Close, Sp, Land, Sp,
            Open, separation, Close, Sp, Land, RowBreak, Grp(),
            Open, updateStability, Close, Sp, Land, RowBreak, Grp(),
            Open, universality, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
