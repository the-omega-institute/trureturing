using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReachableObservableQuotientDescentDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reachable-state dynamics, inputs, and outputs descend to the observable quotient.",
        H("Reachable Observable Quotient Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("reachable-observable-quotient-descent"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Linear/ReachableObservableQuotientDescent."
                    + "reachable_observable_quotient_descent"),
            H("The reachable observable quotient carries the induced system"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The reachable carrier is constructed as the span of all iterated input "
                        + "directions, while the hidden carrier is the intersection of all "
                        + "future output kernels.")),
                Paragraph(Text(
                    "Both invariance clauses and the input-range and output-kernel clauses "
                        + "are public. The three quotient maps are characterized by their "
                        + "computations on canonical quotient representatives."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("State");
        Formula input = F.Id("Input");
        Formula output = F.Id("Output");
        Formula update = F.Id("A");
        Formula control = F.Id("B");
        Formula readout = F.Id("C");
        Formula reachable = F.Id("R");
        Formula hidden = F.Id("N");
        Formula residual = F.Id("D");
        Formula time = F.Id("k");
        Formula pair = F.Id("p");
        Formula point = F.Id("x");
        Formula controlValue = F.Id("u");
        Formula stateProof = F.Id("hAx");
        Formula inputProof = F.Id("hBu");
        Formula inducedDynamics = F.Id("barA");
        Formula descendedInput = F.Id("barB");
        Formula descendedOutput = F.Id("barC");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula stateEndomorphism = Call("LinearMap", scalar, state, state);
        Formula inputMap = Call("LinearMap", scalar, input, state);
        Formula outputMap = Call("LinearMap", scalar, state, output);
        Formula stateSubmodule = Call("Submodule", scalar, state);
        Formula pairType = Call("Prod", naturals, input);
        Formula updatePower = new Formula.Power(update, Grp(Call("fst", pair)));
        Formula iteratedInput = Call(updatePower, Call(control, Call("snd", pair)));
        Formula reachableDefinition = Call(
            "span", scalar,
            Call("range", Grp(
                Lambda, Sp, Typed(pair, pairType), Comma, Sp, iteratedInput)));
        Formula futureKernel = Call(
            "ker", Call("comp", readout, new Formula.Power(update, Grp(time))));
        Formula hiddenDefinition = Call(
            "iInf", Grp(Lambda, Sp, Typed(time, naturals), Comma, Sp, futureKernel));
        Formula residualDefinition = Call(
            "comap", Call("subtype", reachable), hidden);
        Formula quotient = Call("Quotient", reachable, residual);
        Formula quotientEndomorphism = Call("LinearMap", scalar, quotient, quotient);
        Formula quotientInput = Call("LinearMap", scalar, input, quotient);
        Formula quotientOutput = Call("LinearMap", scalar, quotient, output);
        Formula updateAtPoint = Call(update, point);
        Formula inputAtControl = Call(control, controlValue);
        Formula stateRepresentative = Call("subtype", updateAtPoint, stateProof);
        Formula inputRepresentative = Call("subtype", inputAtControl, inputProof);
        Formula dynamicsDescent = Seq(
            Exists, Bang, Sp, Typed(inducedDynamics, quotientEndomorphism), Comma, Sp,
            Forall, Sp, Typed(point, reachable), Comma, Sp,
            Typed(stateProof, Seq(updateAtPoint, Sp, InMacro, Sp, reachable)), Comma, Sp,
            Call(inducedDynamics, Call("mkQ", residual, point)), Sp, Eq, Sp,
            Call("mkQ", residual, stateRepresentative));
        Formula inputDescent = Seq(
            Exists, Bang, Sp, Typed(descendedInput, quotientInput), Comma, Sp,
            Forall, Sp, Typed(controlValue, input), Comma, Sp,
            Typed(inputProof, Seq(inputAtControl, Sp, InMacro, Sp, reachable)), Comma, Sp,
            Call(descendedInput, controlValue), Sp, Eq, Sp,
            Call("mkQ", residual, inputRepresentative));
        Formula outputDescent = Seq(
            Exists, Bang, Sp, Typed(descendedOutput, quotientOutput), Comma, Sp,
            Forall, Sp, Typed(point, reachable), Comma, Sp,
            Call(descendedOutput, Call("mkQ", residual, point)), Sp, Eq, Sp,
            Call(readout, point));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, state, Comma, Sp, input, Comma, Sp, output), type),
                Comma),
            Seq(
                Grp(), Typeclass("Field", scalar), Comma, Sp,
                Typeclass("AddCommGroup", state), Comma, Sp,
                Typeclass("Module", scalar, state), Comma),
            Seq(
                Grp(), Typeclass("AddCommGroup", input), Comma, Sp,
                Typeclass("Module", scalar, input), Comma, Sp,
                Typeclass("AddCommGroup", output), Comma, Sp,
                Typeclass("Module", scalar, output), Comma),
            Seq(
                Forall, Sp, Typed(update, stateEndomorphism), Comma, Sp,
                Typed(control, inputMap), Comma, Sp,
                Typed(readout, outputMap), Comma),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(reachable, stateSubmodule), Sp, Eq, Sp,
                reachableDefinition, Semi),
            Seq(
                Grp(), F.Id("let"), Sp, Typed(hidden, stateSubmodule), Sp, Eq, Sp,
                hiddenDefinition, Semi),
            Seq(
                Grp(), F.Id("let"), Sp,
                Typed(residual, Call("Submodule", scalar, reachable)), Sp, Eq, Sp,
                residualDefinition, Semi),
            Seq(
                Grp(), Call("MapsTo", update, reachable, reachable), Sp, Land, Sp,
                Call("MapsTo", update, hidden, hidden), Sp, Land),
            Seq(
                Grp(), Call("range", control), Sp, Subseteq, Sp, reachable, Sp, Land, Sp,
                residual, Sp, Subseteq, Sp,
                Call("ker", Call("domRestrict", readout, reachable)), Sp, Land),
            Seq(Grp(), dynamicsDescent, Sp, Land),
            Seq(Grp(), inputDescent, Sp, Land),
            Seq(Grp(), outputDescent, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(Formula name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
