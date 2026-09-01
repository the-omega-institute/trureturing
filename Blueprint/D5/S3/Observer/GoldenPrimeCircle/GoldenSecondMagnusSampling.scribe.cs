using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenSecondMagnusSamplingDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden Mellin sample times make second-Magnus curvature descend through whole golden shell shifts.",
        H("Golden Second-Magnus Sampling"),
        Blocks(
            Definition("golden-sample-time", "goldenSampleTime",
                "Golden Mellin sample time",
                "An integral golden Fourier mode is sent to its vertical Mellin time by multiplying it by the fundamental golden angular frequency."),
            Definition("golden-scale-circle-point", "goldenScaleCirclePoint",
                "Visible golden scale-circle point",
                "The unwrapped logarithmic golden coordinate is projected to the unit additive circle."),
            Definition("golden-scale-fourier-phase", "goldenScaleFourierPhase",
                "Golden scale Fourier character",
                "The integral mode character evaluates the visible golden scale coordinate as a unit complex phase."),
            Theorem("circle-point-mul", "golden_scale_circle_point_mul",
                "Positive multiplication becomes circle addition",
                CirclePointMulFormula(),
                "Multiplication of positive scales adds their unwrapped logarithmic coordinates and therefore adds their visible circle points."),
            Theorem("circle-point-shell", "golden_scale_circle_point_phi_even_pow_mul",
                "Whole golden shells have one visible circle point",
                CirclePointShellFormula(),
                "Multiplication by any natural power of phi squared changes the unwrapped coordinate by an integer and is invisible on the unit additive circle."),
            Theorem("phase-log-frequency", "golden_scale_fourier_phase_eq_log_frequency",
                "Golden circle phase equals sampled log-frequency phase",
                PhaseLogFrequencyFormula(),
                "The golden circle character is exactly the existing Fourier character of log scale evaluated at the corresponding golden Mellin sample time."),
            Theorem("phase-norm", "golden_scale_fourier_phase_norm",
                "Golden scale characters have unit norm",
                PhaseNormFormula(),
                "The sampled phase lies on the complex unit circle for every real scale and integral mode."),
            Theorem("phase-mul", "golden_scale_fourier_phase_mul",
                "Golden scale characters are multiplicative",
                PhaseMulFormula(),
                "At one integral mode, the phase of a positive product is the product of the two phases."),
            Theorem("phase-shell", "golden_scale_fourier_phase_phi_even_pow_mul",
                "Integral modes ignore whole golden shell shifts",
                PhaseShellFormula(),
                "Every natural whole-shell shift contributes an integral multiple of a full circle turn, so the complex phase is unchanged."),
            Theorem("kernel-sampling", "second_magnus_kernel_at_golden_samples",
                "Golden sampling realizes the second-Magnus alternant",
                KernelSamplingFormula(),
                "At two golden Mellin sample times, the existing second-Magnus kernel is the alternating determinant of four golden scale character values."),
            Theorem("kernel-shell-invariance", "golden_second_magnus_shell_orbit_invariance",
                "The sampled kernel descends through shell orbits",
                KernelShellFormula(),
                "Independent whole-shell shifts of the two positive scale inputs leave the sampled second-Magnus kernel unchanged."),
            Theorem("energy-shell-invariance", "finite_second_magnus_energy_golden_shell_invariant",
                "Finite sampled energy descends through channelwise shell orbits",
                EnergyShellFormula(),
                "Applying an independent natural whole-shell shift to every positive scale channel preserves the complete finite second-Magnus energy.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));

    private static DocumentBlock.Describe Definition(string id, string declaration,
        string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Positive(Formula value) => Seq(D(0), Sp, Lt, Sp, value);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Pow(Formula value, Formula exponent) => Seq(Grp(value), Caret, Grp(exponent));
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

    private static Formula Statement(Formula[] binders, Formula[] hypotheses, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp); AddSeparated(items, binders, Comma);
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        if (hypotheses.Length > 0)
        {
            AddSeparated(items, hypotheses.Select(h => Seq(Open, h, Close)).ToArray(), Land);
            items.Add(Sp); items.Add(Rightarrow); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static void AddSeparated(List<Formula> items, Formula[] values, Formula separator)
    {
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, separator, Sp]);
            items.Add(values[index]);
        }
    }

    private static Formula X() => F.Id("x");
    private static Formula Y() => F.Id("y");
    private static Formula Shell() => F.Id("n");
    private static Formula ShellX() => new Formula.Subscript(F.Id("n"), F.Id("x"));
    private static Formula ShellY() => new Formula.Subscript(F.Id("n"), F.Id("y"));
    private static Formula Mode() => F.Id("k");
    private static Formula Mode1() => new Formula.Subscript(F.Id("k"), D(1));
    private static Formula Mode2() => new Formula.Subscript(F.Id("k"), D(2));
    private static Formula PhiSquare() => Pow(Varphi, D(2));
    private static Formula ShellShift(Formula shell, Formula x) =>
        Product(Pow(PhiSquare(), shell), x);
    private static Formula CirclePoint(Formula x) => Call("goldenScaleCirclePoint", x);
    private static Formula Phase(Formula x, Formula mode) =>
        Call("goldenScaleFourierPhase", x, mode);
    private static Formula SampleTime(Formula mode) => Call("goldenSampleTime", mode);
    private static Formula Log(Formula x) => Call("log", x);
    private static Formula Kernel(Formula x, Formula y, Formula firstMode, Formula secondMode) =>
        Call("secondMagnusSwapKernel", Log(x), Log(y),
            SampleTime(firstMode), SampleTime(secondMode));

    private static Formula CirclePointMulFormula() =>
        Statement([Typed(X(), Reals()), Typed(Y(), Reals())],
            [Positive(X()), Positive(Y())],
            Seq(CirclePoint(Product(X(), Y())), Sp, Eq, Sp,
                CirclePoint(X()), Sp, Plus, Sp, CirclePoint(Y())));

    private static Formula CirclePointShellFormula() =>
        Statement([Typed(Shell(), Naturals()), Typed(X(), Reals())],
            [Positive(X())],
            Seq(CirclePoint(ShellShift(Shell(), X())), Sp, Eq, Sp,
                CirclePoint(X())));

    private static Formula PhaseLogFrequencyFormula() =>
        Statement([Typed(X(), Reals()), Typed(Mode(), Integers())], [],
            Seq(Phase(X(), Mode()), Sp, Eq, Sp,
                Call("fourierPhase", Log(X()), SampleTime(Mode()))));

    private static Formula PhaseNormFormula() =>
        Statement([Typed(X(), Reals()), Typed(Mode(), Integers())], [],
            Seq(Norm(Phase(X(), Mode())), Sp, Eq, Sp, D(1)));

    private static Formula PhaseMulFormula() =>
        Statement([Typed(X(), Reals()), Typed(Y(), Reals()), Typed(Mode(), Integers())],
            [Positive(X()), Positive(Y())],
            Seq(Phase(Product(X(), Y()), Mode()), Sp, Eq, Sp,
                Product(Phase(X(), Mode()), Phase(Y(), Mode()))));

    private static Formula PhaseShellFormula() =>
        Statement([Typed(Shell(), Naturals()), Typed(X(), Reals()), Typed(Mode(), Integers())],
            [Positive(X())],
            Seq(Phase(ShellShift(Shell(), X()), Mode()), Sp, Eq, Sp,
                Phase(X(), Mode())));

    private static Formula KernelSamplingFormula() =>
        Statement([
                Typed(X(), Reals()), Typed(Y(), Reals()),
                Typed(Mode1(), Integers()), Typed(Mode2(), Integers())], [],
            Seq(Kernel(X(), Y(), Mode1(), Mode2()), Sp, Eq, Sp,
                Product(Phase(X(), Mode1()), Phase(Y(), Mode2())), Sp, Minus, Sp,
                Product(Phase(Y(), Mode1()), Phase(X(), Mode2()))));

    private static Formula KernelShellFormula() =>
        Statement([
                Typed(ShellX(), Naturals()), Typed(ShellY(), Naturals()),
                Typed(X(), Reals()), Typed(Y(), Reals()),
                Typed(Mode1(), Integers()), Typed(Mode2(), Integers())],
            [Positive(X()), Positive(Y())],
            Seq(Kernel(ShellShift(ShellX(), X()), ShellShift(ShellY(), Y()),
                    Mode1(), Mode2()),
                Sp, Eq, Sp, Kernel(X(), Y(), Mode1(), Mode2())));

    private static Formula EnergyShellFormula()
    {
        Formula carrier = F.Id("ι");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula scale = F.Id("s");
        Formula shell = F.Id("n");
        Formula curvature = F.Id("C");
        Formula index = F.Id("p");
        Formula scaleType = new Formula.TypeArrow(carrier, Reals());
        Formula shellType = new Formula.TypeArrow(carrier, Naturals());
        Formula curvatureType = new Formula.TypeArrow(
            carrier, new Formula.TypeArrow(carrier, complexes));
        Formula shiftedFrequency =
            Seq(index, Sp, Mapsto, Sp,
                Log(ShellShift(new Formula.Subscript(shell, index),
                    new Formula.Subscript(scale, index))));
        Formula baseFrequency =
            Seq(index, Sp, Mapsto, Sp,
                Log(new Formula.Subscript(scale, index)));
        Formula positivity = Seq(
            Forall, Sp, index, Colon, Sp, carrier, Comma, Sp,
            Positive(new Formula.Subscript(scale, index)));
        Formula fintype = Seq(
            OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, carrier, Close, CloseBracket);

        return Statement([
                Typed(carrier, type), fintype,
                Typed(scale, scaleType), Typed(shell, shellType),
                Typed(curvature, curvatureType),
                Typed(Mode1(), Integers()), Typed(Mode2(), Integers())],
            [positivity],
            Seq(Call("finiteSecondMagnusEnergy", shiftedFrequency, curvature,
                    SampleTime(Mode1()), SampleTime(Mode2())),
                Sp, Eq, Sp,
                Call("finiteSecondMagnusEnergy", baseFrequency, curvature,
                    SampleTime(Mode1()), SampleTime(Mode2()))));
    }
}
