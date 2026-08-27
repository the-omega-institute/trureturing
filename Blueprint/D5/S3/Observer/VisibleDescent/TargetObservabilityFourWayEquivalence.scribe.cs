using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class TargetObservabilityFourWayEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linear target is observable exactly when its Riesz vector lies in the adjoint range.",
        H("Target Observability Four-Way Equivalence"),
        Blocks(Describe.Lean(
            DescribeId.Create("target-observability-four-way-equivalence"),
            DeclarationHandle.Create(Prefix + "target_observability_four_way_equivalence"),
            H("Four equivalent criteria for linear target observability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The target functional is represented on the source Hilbert space by its "
                        + "displayed Riesz vector. Constancy on observation fibers is equivalent "
                        + "to inclusion of the observation kernel in the target kernel.")),
                Paragraph(Text(
                    "Finite-dimensional orthogonal duality identifies that condition with "
                        + "membership of the Riesz vector in the adjoint range. Every displayed "
                        + "adjoint preimage reconstructs the target from the observation."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("X");
        Formula output = F.Id("Y");
        Formula observation = F.Id("M");
        Formula target = F.Id("t");
        Formula vector = new Formula.Subscript(F.Id("v"), target);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula a = F.Id("a");

        Formula linearObservation = Call("LinearMap", scalar, state, output);
        Formula linearTarget = Call("LinearMap", scalar, state, scalar);
        Formula riesz = Seq(
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(target, x), Sp, Eq, Sp, Call("inner", vector, x));
        Formula determined = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Apply(observation, x), Sp, Eq, Sp, Apply(observation, y), Sp,
            Rightarrow, Sp, Apply(target, x), Sp, Eq, Sp, Apply(target, y));
        Formula kernelInclusion = Seq(
            Call("ker", observation), Sp, Subseteq, Sp, Call("ker", target));
        Formula adjoint = Call("adjoint", observation);
        Formula rangeMembership = Seq(
            vector, Sp, InMacro, Sp, Call("range", adjoint));
        Formula adjointWitness = Seq(
            Exists, Sp, a, Colon, Sp, output, Comma, Sp,
            Apply(adjoint, a), Sp, Eq, Sp, vector);
        Formula reconstruction = Seq(
            Forall, Sp, a, Colon, Sp, output, Comma, Sp,
            Apply(adjoint, a), Sp, Eq, Sp, vector, Sp, Rightarrow, Sp,
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(target, x), Sp, Eq, Sp,
            Call("inner", a, Apply(observation, x)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, state, Comma, Sp, output,
            Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Call("RCLike", scalar), Sp, Land, Sp,
            Call("NormedAddCommGroup", state), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, state), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, state), Sp, Land,
            RowBreak, Grp(),
            Call("NormedAddCommGroup", output), Sp, Land, Sp,
            Call("InnerProductSpace", scalar, output), Sp, Land, Sp,
            Call("FiniteDimensional", scalar, output), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, observation, Colon, Sp, linearObservation, Comma, Sp,
            target, Colon, Sp, linearTarget, Comma, Sp,
            vector, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            Open, riesz, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, Open, determined, Close, Sp, Iff, Sp, kernelInclusion, Close, Sp, Land,
            RowBreak, Grp(),
            Open, Open, determined, Close, Sp, Iff, Sp, rangeMembership, Close, Sp, Land,
            RowBreak, Grp(),
            Open, Open, determined, Close, Sp, Iff, Sp, adjointWitness, Close, Sp, Land,
            RowBreak, Grp(),
            Open, reconstruction, Close, Dot,
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
