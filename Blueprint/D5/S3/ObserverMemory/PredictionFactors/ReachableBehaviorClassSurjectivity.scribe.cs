using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class ReachableBehaviorClassSurjectivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every class of the reachable future-behavior quotient is produced by an allowed action.",
        H("Reachable Behavior Class Surjectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-reachable-behavior-class-is-reachable"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity."
                        + "every_reachable_behavior_class_is_reachable"),
                H("Every reachable behavior class is reachable"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the existing quotient of the actual anchor orbit by equality "
                            + "of every continued public readout.")),
                    Paragraph(Text(
                        "Each quotient representative already contains an allowed action reaching its "
                            + "underlying state. That action produces the representative's canonical "
                            + "behavior class, so the behavior-class map is surjective.")),
                    Paragraph(Text(
                        "The proof reuses the canonical reachable-behavior family and applies pinned "
                            + "Mathlib quotient surjectivity; it introduces no second orbit, behavior, "
                            + "or quotient definition."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality")),
        ]));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula Typeclass1(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Typeclass2(string name, Formula first, Formula second) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, first, Comma, Sp,
            second, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula actionType = F.Id("M");
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula anchor = F.Id("a");
        Formula readout = F.Id("O");
        Formula behavior = F.Id("z");
        Formula action = F.Id("m");
        Formula quotient = Apply(F.Id("ReachableBehaviorQuotient"),
            actionType, anchor, readout);
        Formula behaviorClass = Apply(F.Id("behaviorClass"), anchor, readout, action);

        return Disp(Seq(
            Forall, Sp, actionType, Comma, Sp, stateType, Comma, Sp, outputType, Comma, Sp,
            Typeclass1("Monoid", actionType), Comma, Sp,
            Typeclass2("MulAction", actionType, stateType), Comma, Sp,
            Typed(anchor, stateType), Comma, Sp,
            Typed(readout, new Formula.TypeArrow(stateType, outputType)), Comma, Sp,
            Forall, Sp, Typed(behavior, quotient), Comma, Sp,
            Exists, Sp, Typed(action, actionType), Comma, Sp,
            behaviorClass, Sp, Eq, Sp, behavior, Dot));
    }
}
