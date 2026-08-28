using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorUpdateWordActionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/RefinementClosure/BehaviorUpdateWordAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Controlled behavior updates descend to the realized range and compose along words.",
        H("Behavior Update Word Action"),
        Blocks(Describe.Lean(
            DescribeId.Create("behavior-update-well-defined"),
            DeclarationHandle.Create(Prefix + "behavior_update_well_defined"),
            H("Behavior updates are representative-independent and act by words"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Equality of complete controlled behaviors is preserved after every input. "
                        + "The one-input update is transported through the canonical quotient-to-"
                        + "range equivalence, so it lives on the exact realized behavior range.")),
                Paragraph(Text(
                    "The named word update has the empty-word and concatenation laws. Its value "
                        + "on every realized behavior is the behavior of the source state after "
                        + "the imported left-to-right word execution."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula input = F.Id("U");
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula u = F.Id("u");
        Formula y = F.Id("y");
        Formula yPrime = new Formula.Subscript(F.Id("y"), F.Id("p"));
        Formula behavior = F.Id("b");
        Formula first = F.Id("v");
        Formula second = F.Id("w");

        Formula behaviorOf(Formula point) =>
            Call("controlledBehavior", update, readout, point);
        Formula sourceUpdate(Formula action, Formula point) =>
            Apply(Apply(update, action), point);
        Formula rangePoint(Formula point) =>
            Call("rangeFactorization", Call("controlledBehavior", update, readout), point);
        Formula range = Call("range", Call("controlledBehavior", update, readout));
        Formula oneStep(Formula action, Formula value) =>
            Apply(Call("behaviorUpdate", update, readout, action), value);
        Formula wordStep(Formula word, Formula value) =>
            Apply(Call("behaviorWordUpdate", update, readout, word), value);

        Formula representativeIndependence = Seq(
            Forall, Sp, u, Colon, Sp, input, Comma, Sp,
            y, Comma, Sp, yPrime, Colon, Sp, state, Comma, Sp,
            behaviorOf(y), Sp, Eq, Sp, behaviorOf(yPrime), Sp, Rightarrow, Sp,
            behaviorOf(sourceUpdate(u, y)), Sp, Eq, Sp,
            behaviorOf(sourceUpdate(u, yPrime)));
        Formula oneStepComputation = Seq(
            Forall, Sp, u, Colon, Sp, input, Comma, Sp,
            y, Colon, Sp, state, Comma, Sp,
            oneStep(u, rangePoint(y)), Sp, Eq, Sp, rangePoint(sourceUpdate(u, y)));
        Formula identityLaw = Seq(
            Forall, Sp, behavior, Colon, Sp, range, Comma, Sp,
            wordStep(Call("nil", input), behavior), Sp, Eq, Sp, behavior);
        Formula appendLaw = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, Call("List", input),
            Comma, Sp, behavior, Colon, Sp, range, Comma, Sp,
            wordStep(Call("append", first, second), behavior), Sp, Eq, Sp,
            wordStep(second, wordStep(first, behavior)));
        Formula sourceComputation = Seq(
            Forall, Sp, second, Colon, Sp, Call("List", input), Comma, Sp,
            y, Colon, Sp, state, Comma, Sp,
            wordStep(second, rangePoint(y)), Sp, Eq, Sp,
            rangePoint(Call("runWord", update, second, y)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, input, Comma, Sp, state, Comma, Sp, output,
            Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Forall, Sp, update, Colon, Sp,
            new Formula.TypeArrow(input,
                new Formula.TypeArrow(state, state)), Comma, Sp,
            readout, Colon, Sp, new Formula.TypeArrow(state, output), Comma,
            RowBreak, Grp(),
            Open, representativeIndependence, Close, Sp, Land,
            RowBreak, Grp(),
            Open, oneStepComputation, Close, Sp, Land,
            RowBreak, Grp(),
            Open, identityLaw, Close, Sp, Land,
            RowBreak, Grp(),
            Open, appendLaw, Close, Sp, Land,
            RowBreak, Grp(),
            Open, sourceComputation, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
