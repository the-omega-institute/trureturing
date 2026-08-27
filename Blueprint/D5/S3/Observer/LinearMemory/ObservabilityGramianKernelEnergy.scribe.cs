using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class ObservabilityGramianKernelEnergyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/ObservabilityGramianKernelEnergy."
            + "observability_gramian_kernel_energy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stable ordinary observability Gramian has the all-future readout kernel, "
            + "its quadratic form is total future output energy, and that energy vanishes "
            + "exactly on states with no future output.",
        H("Observability Gramian Kernel and Energy"),
        Blocks(Describe.Lean(
            DescribeId.Create("observability-gramian-kernel-energy"),
            DeclarationHandle.Create(Declaration),
            H("The ordinary Gramian kernel is the all-future kernel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The ordinary Gramian is the canonical weight-one instance of the "
                        + "repository's Gramian series. Stability is stated directly as "
                        + "summability of that exact operator series, without imposing a "
                        + "stronger contraction-norm condition.")),
                Paragraph(Text(
                    "Continuous evaluation, inner product, and real-part maps carry the "
                        + "summable operator series term by term. Each term is the squared "
                        + "norm of one future readout, so nonnegativity makes zero total "
                        + "energy equivalent to vanishing at every future time."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula output = F.Id("Y");
        Formula evolution = F.Id("T");
        Formula readout = F.Id("C");
        Formula stability = F.Id("hStable");
        Formula point = F.Id("x");
        Formula time = F.Id("k");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula evolutionPower = Seq(evolution, Caret, Grp(time));
        Formula future = Apply(readout, Apply(evolutionPower, point));
        Formula term = Call("discountedGramianTerm", evolution, readout, D(1), time);
        Formula stableSeries = Seq(time, Sp, Mapsto, Sp, term);
        Formula gramian = Call(
            "discountedObservabilityGramian", evolution, readout, D(1));
        Formula gramianAt = Apply(gramian, point);
        Formula quadratic = Seq(
            Re, Open, Langle, Sp, point, Comma, Sp, gramianAt, Sp, Rangle, Close);
        Formula energyTerm = Seq(new Formula.Norm(future), Caret, Grp(D(2)));
        Formula energy = Seq(
            Sum, Underscore, Grp(Seq(time, Eq, D(0))),
            Caret, Grp(Infty), Sp, energyTerm);
        Formula futureKernel = Seq(
            Operatorname, Grp(F.Id("intersection")),
            Underscore, Grp(Seq(time, Sp, InMacro, Sp, natural)), Sp,
            Call("ker", Call("comp", readout, evolutionPower)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(scalar, Comma, Sp, state, Comma, Sp, output), type),
                Comma),
            Seq(
                Grp(), Typeclass("RCLike", scalar), Comma, Sp,
                Typeclass("NormedAddCommGroup", state), Comma),
            Seq(
                Grp(), Typeclass("InnerProductSpace", scalar, state), Comma, Sp,
                Typeclass("FiniteDimensional", scalar, state), Comma),
            Seq(
                Grp(), Typeclass("NormedAddCommGroup", output), Comma, Sp,
                Typeclass("InnerProductSpace", scalar, output), Comma),
            Seq(
                Grp(), Typeclass("FiniteDimensional", scalar, output), Comma),
            Seq(
                Forall, Sp,
                Typed(evolution, Call("LinearMap", scalar, state, state)), Comma, Sp,
                Typed(readout, Call("LinearMap", scalar, state, output)), Comma),
            Seq(
                Grp(), Typed(stability, Call("Summable", stableSeries)), Comma),
            Seq(
                Call("ker", Call("toLinearMap", gramian)), Sp, Eq, Sp,
                futureKernel, Sp, Land),
            Seq(
                Grp(), Open, Forall, Sp, Typed(point, state), Comma, Sp,
                quadratic, Sp, Eq, Sp, energy, Close, Sp, Land),
            Seq(
                Grp(), Open, Forall, Sp, Typed(point, state), Comma, Sp,
                quadratic, Sp, Eq, Sp, D(0), Sp, Iff, Sp,
                Forall, Sp, Typed(time, natural), Comma, Sp,
                future, Sp, Eq, Sp, D(0), Close, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
