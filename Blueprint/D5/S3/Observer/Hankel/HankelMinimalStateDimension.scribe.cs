using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class HankelMinimalStateDimensionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Hankel/HankelMinimalStateDimension."
            + "hankel_rank_lower_bound_and_quotient_attainment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite-dimensional realization with the same Markov parameters has "
            + "dimension at least the stable Hankel rank. The named reachable-observable "
            + "quotient realization attains that minimum, while raw state dimension is "
            + "presentation-dependent.",
        H("Hankel Minimal State Dimension"),
        Blocks(Describe.Lean(
            DescribeId.Create("hankel-minimal-state-dimension"),
            DeclarationHandle.Create(Declaration),
            H("The Hankel rank is the minimum realization dimension"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A, B, and C define a finite-dimensional discrete linear system. "
                        + "Assume the competing realization A', B', and C' has the same "
                        + "complete input-output behavior, expressed by equality of every "
                        + "Markov parameter.")),
                Paragraph(Text(
                    "For row and column horizons at least finrank(K,V), the common finite "
                        + "Hankel rank is no larger than finrank(K,V'). The named quotient "
                        + "realization (A_min, B_min, C_min) has every original Markov "
                        + "parameter and state dimension equal to that rank.")),
                Paragraph(Text(
                    "A one-dimensional padded realization witnesses that raw state dimension "
                        + "is not invariant under complete input-output behavior. The infimum "
                        + "of all finite same-behavior state dimensions is exactly the Hankel "
                        + "rank, and the named quotient realizes it."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula competingState = Seq(F.Id("V"), Apos);
        Formula input = F.Id("U");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("A");
        Formula control = F.Id("B");
        Formula readout = F.Id("C");
        Formula competingEvolution = Seq(F.Id("A"), Apos);
        Formula competingControl = Seq(F.Id("B"), Apos);
        Formula competingReadout = Seq(F.Id("C"), Apos);
        Formula time = F.Id("k");
        Formula rows = F.Id("r");
        Formula columns = F.Id("s");
        Formula stateDimension = Call("finrank", scalar, state);
        Formula competingDimension = Call("finrank", scalar, competingState);
        Formula quotient = Call("MinimalStateSpace", evolution, control, readout);
        Formula hankel = Call(
            "finiteHankel", evolution, control, readout, rows, columns);
        Formula hankelRank = Call("finrank", scalar, Call("range", hankel));
        Formula sameBehavior = Seq(
            Forall, Sp, time, Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
            Call("markovParameter", competingEvolution, competingControl,
                competingReadout, time),
            Sp, Eq, Sp,
            Call("markovParameter", evolution, control, readout, time));
        Formula originalBehavior = Lambda(time,
            Call("markovParameter", evolution, control, readout, time));
        Formula minimalBehavior = Lambda(time,
            Call("markovParameter",
                Call("minimalDynamics", evolution, control, readout),
                Call("minimalInput", evolution, control, readout),
                Call("minimalOutput", evolution, control, readout), time));
        Formula lowerBound = Seq(hankelRank, Sp, Leq, Sp, competingDimension);
        Formula quotientSignature = Seq(
            Open, minimalBehavior, Comma, Sp, Call("finrank", scalar, quotient), Close,
            Sp, Eq, Sp,
            Open, originalBehavior, Comma, Sp, hankelRank, Close);
        Formula rawDimensionNotInvariant = Seq(
            Neg, Sp, Call("StateDimensionInvariantAt", originalBehavior));
        Formula minimumDimension = Seq(
            Call("sInf", Call("sameBehaviorDimensions", evolution, control, readout)),
            Sp, Eq, Sp, hankelRank);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, competingState,
            Comma, Sp, input, Comma, Sp, output, Colon, Sp, F.Id("Type"),
            Comma, RowBreak, Grp(),
            Call("Field", scalar), Sp, Land, Sp,
            Call("AddCommGroup", state), Sp, Land, Sp,
            Call("Module", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land, RowBreak, Grp(),
            Call("AddCommGroup", competingState), Sp, Land, Sp,
            Call("Module", scalar, competingState), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, competingState), Sp, Land,
            RowBreak, Grp(),
            Call("AddCommGroup", input), Sp, Land, Sp,
            Call("Module", scalar, input), Sp, Land, Sp,
            Call("AddCommGroup", output), Sp, Land, Sp,
            Call("Module", scalar, output), Sp, Land, RowBreak, Grp(),
            evolution, Sp, InMacro, Sp,
            Call("LinearMap", scalar, state, state), Sp, Land, Sp,
            control, Sp, InMacro, Sp,
            Call("LinearMap", scalar, input, state), Sp, Land, Sp,
            readout, Sp, InMacro, Sp,
            Call("LinearMap", scalar, state, output), Comma, RowBreak, Grp(),
            competingEvolution, Sp, InMacro, Sp,
            Call("LinearMap", scalar, competingState, competingState), Sp,
            Land, Sp, competingControl, Sp, InMacro, Sp,
            Call("LinearMap", scalar, input, competingState), Sp, Land, Sp,
            competingReadout, Sp, InMacro, Sp,
            Call("LinearMap", scalar, competingState, output), Comma,
            RowBreak, Grp(),
            sameBehavior, Comma, RowBreak, Grp(),
            rows, Comma, Sp, columns, Sp, InMacro, Sp, F.Id("N"), Comma, Sp,
            stateDimension, Sp, Leq, Sp, rows, Sp, Land, Sp,
            stateDimension, Sp, Leq, Sp, columns, Sp,
            Rightarrow, RowBreak, Grp(),
            lowerBound, Sp, Land, RowBreak, Grp(),
            quotientSignature, Sp, Land, RowBreak, Grp(),
            rawDimensionNotInvariant, Sp, Land, RowBreak, Grp(),
            minimumDimension, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

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
}
