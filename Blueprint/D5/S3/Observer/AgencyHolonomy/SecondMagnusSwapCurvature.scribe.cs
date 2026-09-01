using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class SecondMagnusSwapCurvatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An alternating Fourier slot kernel modulates finite holonomy into a bounded second-Magnus energy.",
        H("Second-Magnus Swap Curvature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("second-magnus-swap-kernel"),
                DeclarationHandle.Create(Prefix + "secondMagnusSwapKernel"),
                H("Second-Magnus Fourier slot kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The kernel is the determinant obtained by assigning two frequency "
                        + "characters to two fixed time slots and subtracting the swapped "
                        + "assignment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-second-magnus-energy"),
                DeclarationHandle.Create(Prefix + "finiteSecondMagnusEnergy"),
                H("Finite second-Magnus energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each ordered-pair curvature is multiplied by its two-slot Fourier "
                        + "kernel, squared in norm, and summed over the finite carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stable-residual-second-magnus-energy"),
                DeclarationHandle.Create(Prefix + "stableResidualSecondMagnusEnergy"),
                H("Stable residual second-Magnus energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite second-Magnus construction is specialized to the existing "
                        + "stable residual swap-curvature field."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("swap-frequency"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_swap_frequency"),
                H("Frequency-exchange antisymmetry"),
                StatementSource.FromAuthor(SwapFrequencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exchanging the two frequency labels reverses the orientation and "
                        + "negates the slot kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("swap-time"),
                DeclarationHandle.Create(Prefix + "second_magnus_swap_kernel_swap_time"),
                H("Time-slot antisymmetry"),
                StatementSource.FromAuthor(SwapTimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exchanging the two time slots reverses the orientation and negates "
                        + "the slot kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-times"),
                DeclarationHandle.Create(Prefix + "second_magnus_swap_kernel_equal_times"),
                H("Equal-time vanishing"),
                StatementSource.FromAuthor(EqualTimesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The alternating determinant vanishes when both evaluations use the "
                        + "same time slot."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-frequencies"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_equal_frequencies"),
                H("Equal-frequency vanishing"),
                StatementSource.FromAuthor(EqualFrequenciesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The alternating determinant vanishes when both channels carry the "
                        + "same frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-norm-bound"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_norm_le_two"),
                H("Uniform kernel norm bound"),
                StatementSource.FromAuthor(NormBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both phase products have unit norm, so their difference has norm at "
                        + "most two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-decomposition"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_center_decomposition"),
                H("Center and relative decomposition"),
                StatementSource.FromAuthor(CenterDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mean time and mean frequency form a common unitary phase. The remaining "
                        + "bracket depends only on the time difference and half the frequency "
                        + "difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sine-form"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_sine_form"),
                H("Odd sine form"),
                StatementSource.FromAuthor(SineFormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The relative bracket is exactly minus two times the imaginary unit "
                        + "times the sine of half the time-frequency area, multiplied by the "
                        + "common mean phase."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-energy-bound"),
                DeclarationHandle.Create(Prefix + "finite_second_magnus_energy_bound"),
                H("Finite energy domination"),
                StatementSource.FromAuthor(FiniteEnergyBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite second-Magnus energy is nonnegative and bounded above by four "
                        + "times the underlying finite holonomy energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stable-residual-energy-bound"),
                DeclarationHandle.Create(
                    Prefix + "stable_residual_second_magnus_energy_bound"),
                H("Residual envelope to second-Magnus decay"),
                StatementSource.FromAuthor(ResidualEnergyBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Composing finite energy domination with the stable residual holonomy "
                        + "bound makes a vanishing residual envelope sufficient for vanishing "
                        + "finite second-Magnus energy."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy")),
        ]));


    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Typed(Formula value) =>
        Seq(value, Colon, Sp, Reals());

    private static Formula Norm(Formula value) => new Formula.Norm(value);

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

    private static Formula FreqP() => new Formula.Subscript(F.Id("f"), F.Id("p"));
    private static Formula FreqQ() => new Formula.Subscript(F.Id("f"), F.Id("q"));
    private static Formula Time1() => new Formula.Subscript(F.Id("t"), D(1));
    private static Formula Time2() => new Formula.Subscript(F.Id("t"), D(2));

    private static Formula Kernel(Formula a, Formula b, Formula c, Formula d) =>
        Call("secondMagnusSwapKernel", a, b, c, d);

    private static Formula QuadBinder() => Seq(
        Forall, Sp, Typed(FreqP()), Comma, Sp, Typed(FreqQ()), Comma, Sp,
        Typed(Time1()), Comma, Sp, Typed(Time2()), Comma, Sp);

    private static Formula SwapFrequencyFormula() => Disp(Seq(
        QuadBinder(),
        Kernel(FreqQ(), FreqP(), Time1(), Time2()), Sp, Eq, Sp,
        Minus, Kernel(FreqP(), FreqQ(), Time1(), Time2()), Dot));

    private static Formula SwapTimeFormula() => Disp(Seq(
        QuadBinder(),
        Kernel(FreqP(), FreqQ(), Time2(), Time1()), Sp, Eq, Sp,
        Minus, Kernel(FreqP(), FreqQ(), Time1(), Time2()), Dot));

    private static Formula EqualTimesFormula() => Disp(Seq(
        Forall, Sp, Typed(FreqP()), Comma, Sp, Typed(FreqQ()), Comma, Sp,
        Typed(F.Id("t")), Comma, Sp,
        Kernel(FreqP(), FreqQ(), F.Id("t"), F.Id("t")), Sp, Eq, Sp, D(0), Dot));

    private static Formula EqualFrequenciesFormula() => Disp(Seq(
        Forall, Sp, Typed(F.Id("f")), Comma, Sp,
        Typed(Time1()), Comma, Sp, Typed(Time2()), Comma, Sp,
        Kernel(F.Id("f"), F.Id("f"), Time1(), Time2()), Sp, Eq, Sp, D(0), Dot));

    private static Formula NormBoundFormula() => Disp(Seq(
        QuadBinder(),
        Norm(Kernel(FreqP(), FreqQ(), Time1(), Time2())), Sp, Leq, Sp,
        D(2), Dot));

    private static Formula MeanFrequency() =>
        Seq(Frac, Grp(Seq(FreqP(), Sp, Plus, Sp, FreqQ())), Grp(D(2)));

    private static Formula HalfDifferenceFrequency() =>
        Seq(Frac, Grp(Seq(FreqP(), Sp, Minus, Sp, FreqQ())), Grp(D(2)));

    private static Formula TimeSum() => Seq(Time1(), Sp, Plus, Sp, Time2());

    private static Formula TimeDifference() => Seq(Time1(), Sp, Minus, Sp, Time2());

    private static Formula CenterDecompositionFormula() => Disp(Seq(
        QuadBinder(),
        Kernel(FreqP(), FreqQ(), Time1(), Time2()), Sp, Eq, Sp,
        Call("fourierPhase", MeanFrequency(), TimeSum()), Sp, Cdot, Sp,
        Open,
        Call("fourierPhase", HalfDifferenceFrequency(), TimeDifference()),
        Sp, Minus, Sp,
        Call("fourierPhase", Seq(Minus, HalfDifferenceFrequency()),
            TimeDifference()),
        Close, Dot));

    private static Formula SineFormFormula() => Disp(Seq(
        QuadBinder(),
        Kernel(FreqP(), FreqQ(), Time1(), Time2()), Sp, Eq, Sp,
        Open, Minus, D(2), F.Id("i"), Close, Sp, Cdot, Sp,
        Exp, Open, Minus, F.Id("i"), Sp, Cdot, Sp,
        Seq(Open, TimeSum(), Close), Sp, Cdot, Sp,
        MeanFrequency(), Close, Sp, Cdot, Sp,
        Sin, Open, Seq(Open, TimeDifference(), Close), Sp, Cdot, Sp,
        HalfDifferenceFrequency(), Close, Dot));

    private static Formula FiniteEnergyBoundFormula()
    {
        Formula freq = F.Id("f");
        Formula curvature = F.Id("c");
        Formula energy = Call("finiteSecondMagnusEnergy",
            freq, curvature, Time1(), Time2());
        return Disp(Seq(
            Forall, Sp, freq, Comma, Sp, curvature, Comma, Sp,
            Typed(Time1()), Comma, Sp, Typed(Time2()), Comma, Sp,
            D(0), Sp, Leq, Sp, energy, Sp, Land, Sp,
            energy, Sp, Leq, Sp,
            D(4), Sp, Cdot, Sp, Call("finiteHolonomyEnergy", curvature), Dot));
    }

    private static Formula ResidualEnergyBoundFormula()
    {
        Formula stable = F.Id("s");
        Formula residual = F.Id("r");
        Formula channel = F.Id("v");
        Formula freq = F.Id("f");
        Formula envelope = F.Id("e");
        Formula index = F.Id("p");
        Formula residualP = new Formula.Subscript(F.Id("r"), F.Id("p"));
        Formula channelP = new Formula.Subscript(F.Id("v"), F.Id("p"));
        Formula energy = Call("stableResidualSecondMagnusEnergy",
            stable, residual, channel, freq, Time1(), Time2());
        Formula cardSquare = Seq(
            Call("card", Iota), Caret, Grp(D(2)));
        Formula envelopeBound = Seq(
            D(2), Sp, Cdot, Sp, Norm(Seq(stable, Sp, Minus, Sp, D(1))),
            Sp, Cdot, Sp, envelope, Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, envelope, Caret, Grp(D(2)));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stable, Comma, Sp, residual, Comma, Sp, channel,
            Comma, Sp, freq, Comma, Sp, Typed(Time1()), Comma, Sp,
            Typed(Time2()), Comma, Sp, Typed(envelope), Colon,
            RowBreak, Grp(),
            Open, D(0), Sp, Leq, Sp, envelope, Sp, Land, Sp,
            Open, Forall, Sp, index, Comma, Sp,
            Norm(channelP), Sp, Leq, Sp, D(1), Close, Sp, Land, Sp,
            Open, Forall, Sp, index, Comma, Sp,
            Norm(residualP), Sp, Leq, Sp, envelope, Close, Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            D(0), Sp, Leq, Sp, energy, Sp, Land, Sp,
            energy, Sp, Leq, Sp,
            D(4), Sp, Cdot, Sp,
            Open, cardSquare, Sp, Cdot, Sp,
            Open, envelopeBound, Close, Caret, Grp(D(2)), Close, Sp, Land,
            RowBreak, Grp(),
            Open, envelope, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            energy, Sp, Eq, Sp, D(0), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
