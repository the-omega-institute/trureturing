using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class ReachableQuotientObservabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero future output identifies the zero class in the reachable-state quotient.",
        H("Reachable Quotient Observability"),
        Blocks(Describe.Lean(
            DescribeId.Create("zero-future-output-forces-the-zero-quotient-class"),
            DeclarationHandle.Create(
                "D5/S3/Observer/LinearMemory/ReachableQuotientObservability."
                    + "reachable_quotient_observability"),
            H("The reachable quotient is observable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The reachable carrier is the span of all iterated input directions. The "
                        + "hidden carrier is the intersection of every future readout kernel, "
                        + "and the residual is its pullback to the reachable carrier.")),
                Paragraph(Text(
                    "If every future output of a reachable representative is zero, that "
                        + "representative belongs to the hidden carrier. Membership in the "
                        + "residual then makes its canonical quotient class zero."))),
            DescribeRole.Theorem))));

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
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula stateEndomorphism = Call("LinearMap", scalar, state, state);
        Formula inputMap = Call("LinearMap", scalar, input, state);
        Formula outputMap = Call("LinearMap", scalar, state, output);
        Formula stateSubmodule = Call("Submodule", scalar, state);
        Formula pairType = Call("Prod", naturals, input);
        Formula updateAtPair = new Formula.Power(update, Grp(Call("fst", pair)));
        Formula iteratedInput = Call(updateAtPair, Call(control, Call("snd", pair)));
        Formula reachableDefinition = Call(
            "span", scalar,
            Call("range", Grp(
                Lambda, Sp, Typed(pair, pairType), Comma, Sp, iteratedInput)));
        Formula updateAtTime = new Formula.Power(update, Grp(time));
        Formula futureKernel = Call("ker", Call("comp", readout, updateAtTime));
        Formula hiddenDefinition = Call(
            "iInf", Grp(Lambda, Sp, Typed(time, naturals), Comma, Sp, futureKernel));
        Formula residualDefinition = Call(
            "comap", Call("subtype", reachable), hidden);
        Formula futureZero = Seq(
            Forall, Sp, Typed(time, naturals), Comma, Sp,
            Call(readout, Call(updateAtTime, point)), Sp, Eq, Sp, D(0));
        Formula quotientZero = Seq(
            Call("mkQ", residual, point), Sp, Eq, Sp, D(0));

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
                Grp(), Forall, Sp, Typed(point, reachable), Comma, Sp,
                Open, futureZero, Close, Sp, Rightarrow, Sp, quotientZero, Dot),
        ]));
    }
}
