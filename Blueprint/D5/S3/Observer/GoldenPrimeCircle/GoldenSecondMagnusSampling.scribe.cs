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
            Describe.Lean(
                DescribeId.Create("golden-sample-time"),
                DeclarationHandle.Create(Prefix + "goldenSampleTime"),
                H("Golden Mellin sample time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An integral golden Fourier mode is sent to its vertical Mellin time "
                        + "by multiplying it by the fundamental golden angular frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-scale-circle-point"),
                DeclarationHandle.Create(Prefix + "goldenScaleCirclePoint"),
                H("Visible golden scale-circle point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unwrapped logarithmic golden coordinate is projected to the unit "
                        + "additive circle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-scale-fourier-phase"),
                DeclarationHandle.Create(Prefix + "goldenScaleFourierPhase"),
                H("Golden scale Fourier character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral mode character evaluates the visible golden scale "
                        + "coordinate as a unit complex phase."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circle-point-mul"),
                DeclarationHandle.Create(Prefix + "golden_scale_circle_point_mul"),
                H("Positive multiplication becomes circle addition"),
                StatementSource.FromAuthor(CirclePointMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication of positive scales adds their unwrapped logarithmic "
                        + "coordinates and therefore adds their visible circle points."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circle-point-shell"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_circle_point_phi_even_pow_mul"),
                H("Whole golden shells have one visible circle point"),
                StatementSource.FromAuthor(CirclePointShellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by any natural power of phi squared changes the "
                        + "unwrapped coordinate by an integer and is invisible on the unit "
                        + "additive circle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-log-frequency"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_fourier_phase_eq_log_frequency"),
                H("Golden circle phase equals sampled log-frequency phase"),
                StatementSource.FromAuthor(PhaseLogFrequencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The golden circle character is exactly the existing Fourier character "
                        + "of log scale evaluated at the corresponding golden Mellin sample "
                        + "time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-norm"),
                DeclarationHandle.Create(Prefix + "golden_scale_fourier_phase_norm"),
                H("Golden scale characters have unit norm"),
                StatementSource.FromAuthor(PhaseNormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sampled phase lies on the complex unit circle for every real "
                        + "scale and integral mode."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-mul"),
                DeclarationHandle.Create(Prefix + "golden_scale_fourier_phase_mul"),
                H("Golden scale characters are multiplicative"),
                StatementSource.FromAuthor(PhaseMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At one integral mode, the phase of a positive product is the product "
                        + "of the two phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-shell"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_fourier_phase_phi_even_pow_mul"),
                H("Integral modes ignore whole golden shell shifts"),
                StatementSource.FromAuthor(PhaseShellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every natural whole-shell shift contributes an integral multiple of a "
                        + "full circle turn, so the complex phase is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-sampling"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_kernel_at_golden_samples"),
                H("Golden sampling realizes the second-Magnus alternant"),
                StatementSource.FromAuthor(KernelSamplingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At two golden Mellin sample times, the existing second-Magnus kernel "
                        + "is the alternating determinant of four golden scale character "
                        + "values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-shell-invariance"),
                DeclarationHandle.Create(
                    Prefix + "golden_second_magnus_shell_orbit_invariance"),
                H("The sampled kernel descends through shell orbits"),
                StatementSource.FromAuthor(KernelShellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Independent whole-shell shifts of the two positive scale inputs leave "
                        + "the sampled second-Magnus kernel unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("energy-shell-invariance"),
                DeclarationHandle.Create(
                    Prefix + "finite_second_magnus_energy_golden_shell_invariant"),
                H("Finite sampled energy descends through channelwise shell orbits"),
                StatementSource.FromAuthor(EnergyShellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying an independent natural whole-shell shift to every positive "
                        + "scale channel preserves the complete finite second-Magnus "
                        + "energy."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));

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

    private static Formula CirclePoint(Formula scale) =>
        Call("goldenScaleCirclePoint", scale);

    private static Formula Phase(Formula scale, Formula mode) =>
        Call("goldenScaleFourierPhase", scale, mode);

    private static Formula SampleTime(Formula mode) =>
        Call("goldenSampleTime", mode);

    private static Formula LogOf(Formula scale) =>
        Seq(Log, Open, scale, Close);

    private static Formula ShellShift(Formula shell, Formula scale) =>
        Seq(Open, F.Id("phi"), Caret, Grp(D(2)), Close,
            Caret, Grp(shell), Sp, Cdot, Sp, scale);

    private static Formula PositivePair() => Seq(
        D(0), Sp, Lt, Sp, F.Id("x"), Sp, Land, Sp,
        D(0), Sp, Lt, Sp, F.Id("y"), Sp, Rightarrow, Sp);

    private static Formula CirclePointMulFormula() => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        PositivePair(),
        CirclePoint(Seq(F.Id("x"), Sp, Cdot, Sp, F.Id("y"))), Sp, Eq, Sp,
        CirclePoint(F.Id("x")), Sp, Plus, Sp, CirclePoint(F.Id("y")), Dot));

    private static Formula CirclePointShellFormula() => Disp(Seq(
        Forall, Sp, F.Id("k"), Comma, Sp, F.Id("x"), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("x"), Sp, Rightarrow, Sp,
        CirclePoint(ShellShift(F.Id("k"), F.Id("x"))), Sp, Eq, Sp,
        CirclePoint(F.Id("x")), Dot));

    private static Formula PhaseLogFrequencyFormula() => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("m"), Comma, Sp,
        Phase(F.Id("x"), F.Id("m")), Sp, Eq, Sp,
        Call("fourierPhase", LogOf(F.Id("x")), SampleTime(F.Id("m"))), Dot));

    private static Formula PhaseNormFormula() => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("m"), Comma, Sp,
        Norm(Phase(F.Id("x"), F.Id("m"))), Sp, Eq, Sp, D(1), Dot));

    private static Formula PhaseMulFormula() => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp, F.Id("m"),
        Comma, Sp,
        PositivePair(),
        Phase(Seq(F.Id("x"), Sp, Cdot, Sp, F.Id("y")), F.Id("m")),
        Sp, Eq, Sp,
        Phase(F.Id("x"), F.Id("m")), Sp, Cdot, Sp,
        Phase(F.Id("y"), F.Id("m")), Dot));

    private static Formula PhaseShellFormula() => Disp(Seq(
        Forall, Sp, F.Id("k"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("m"),
        Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("x"), Sp, Rightarrow, Sp,
        Phase(ShellShift(F.Id("k"), F.Id("x")), F.Id("m")), Sp, Eq, Sp,
        Phase(F.Id("x"), F.Id("m")), Dot));

    private static Formula SampledKernel(Formula first, Formula second) =>
        Call("secondMagnusSwapKernel",
            LogOf(first), LogOf(second),
            SampleTime(new Formula.Subscript(F.Id("m"), D(1))),
            SampleTime(new Formula.Subscript(F.Id("m"), D(2))));

    private static Formula KernelSamplingFormula()
    {
        Formula m1 = new Formula.Subscript(F.Id("m"), D(1));
        Formula m2 = new Formula.Subscript(F.Id("m"), D(2));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            m1, Comma, Sp, m2, Colon,
            RowBreak, Grp(),
            SampledKernel(F.Id("x"), F.Id("y")), Sp, Eq, Sp,
            Phase(F.Id("x"), m1), Sp, Cdot, Sp, Phase(F.Id("y"), m2),
            Sp, Minus, Sp,
            Phase(F.Id("y"), m1), Sp, Cdot, Sp, Phase(F.Id("x"), m2), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula KernelShellFormula()
    {
        Formula kx = new Formula.Subscript(F.Id("k"), F.Id("x"));
        Formula ky = new Formula.Subscript(F.Id("k"), F.Id("y"));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, kx, Comma, Sp, ky, Comma, Sp,
            F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            new Formula.Subscript(F.Id("m"), D(1)), Comma, Sp,
            new Formula.Subscript(F.Id("m"), D(2)), Comma, Sp,
            PositivePair(),
            RowBreak, Grp(),
            SampledKernel(ShellShift(kx, F.Id("x")), ShellShift(ky, F.Id("y"))),
            Sp, Eq, Sp,
            SampledKernel(F.Id("x"), F.Id("y")), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula EnergyShellFormula()
    {
        Formula p = F.Id("p");
        Formula sp = new Formula.Subscript(F.Id("s"), F.Id("p"));
        Formula kp = new Formula.Subscript(F.Id("k"), F.Id("p"));
        Formula m1 = new Formula.Subscript(F.Id("m"), D(1));
        Formula m2 = new Formula.Subscript(F.Id("m"), D(2));
        Formula shifted = Seq(p, Sp, Mapsto, Sp,
            LogOf(ShellShift(kp, sp)));
        Formula plain = Seq(p, Sp, Mapsto, Sp, LogOf(sp));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("s"), Comma, Sp, F.Id("k"), Comma, Sp,
            F.Id("c"), Comma, Sp, m1, Comma, Sp, m2, Comma, Sp,
            Open, Forall, Sp, p, Comma, Sp,
            D(0), Sp, Lt, Sp, sp, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("finiteSecondMagnusEnergy",
                Grp(shifted), F.Id("c"),
                SampleTime(m1), SampleTime(m2)),
            RowBreak, Grp(),
            Eq, Sp,
            Call("finiteSecondMagnusEnergy",
                Grp(plain), F.Id("c"),
                SampleTime(m1), SampleTime(m2)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
