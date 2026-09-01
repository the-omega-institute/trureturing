using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ReflectedPairCurvatureRayleighIntertwinerDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realize the off-line curvature dipole as a normalized even-channel "
            + "quadratic readout.",
        H("Reflected-Pair Curvature Rayleigh Intertwiner"),
        Blocks(
            DefinitionNode(
                "detuned-reflected-generator",
                "detunedReflectedGenerator",
                "The detuned reflected generator",
                "The two-by-two complex generator is i tau times the identity plus delta "
                    + "times the frozen Pauli-X coupling. It carries spectral detuning and "
                    + "radial reflection in one finite operator."),
            DefinitionNode(
                "even-channel-state",
                "evenChannelState",
                "The even channel",
                "The standard first basis vector is the branch-symmetric readout channel."),
            DefinitionNode(
                "negative-square-readout",
                "evenChannelNegativeSquareReadout",
                "The even-channel negative-square readout",
                "The repository Hermitian form reads minus the square of the finite generator "
                    + "on the even channel."),
            DefinitionNode(
                "energy-readout",
                "evenChannelEnergyReadout",
                "The even-channel energy readout",
                "The same Hermitian form reads the positive Gram operator A-star A on the "
                    + "even channel."),
            DefinitionNode(
                "normalized-curvature-readout",
                "normalizedCurvatureRayleighReadout",
                "The normalized curvature Rayleigh readout",
                "Twice the signed negative-square readout is divided by the square of the "
                    + "positive energy readout."),
            DefinitionNode(
                "center-polarity-kernel",
                "centerCurvaturePolarityKernel",
                "The coarse center-polarity kernel",
                "Zero splitting selects the zero one-point kernel. Every nonzero split selects "
                    + "the canonical oneNegativeKernel already owned by the Pick library."),
            TheoremNode(
                "normalized-rayleigh-formula",
                "normalized_curvature_rayleigh_readout_formula",
                "The normalized readout is the rational dipole profile",
                NormalizedFormula(),
                "The negative-square numerator is tau squared minus delta squared, while the "
                    + "positive energy is tau squared plus delta squared."),
            TheoremNode(
                "off-line-curvature-intertwiner",
                "off_line_curvature_rayleigh_intertwiner",
                "The analytic dipole and finite Rayleigh chart agree",
                IntertwinerFormula(),
                "The already frozen second normal derivative of the reflected logarithmic "
                    + "potential equals the normalized finite readout at detuning t minus gamma."),
            TheoremNode(
                "hyperbolic-negative-center",
                "offline_zero_monodromy_hyperbolic_iff_negative_center",
                "Hyperbolic monodromy is negative center curvature",
                HyperbolicFormula(),
                "The frozen hyperbolic-bulk criterion and the center-sign criterion are the "
                    + "same nonzero critical-displacement test."),
            TheoremNode(
                "unitary-zero-center",
                "offline_zero_character_unitary_iff_zero_center",
                "The unitary boundary is zero center curvature",
                UnitaryFormula(),
                "The frozen unitary-axis criterion is exactly the zero set of the normalized "
                    + "center readout."),
            TheoremNode(
                "center-polarity-agreement",
                "normalized_center_readout_eq_polarity_kernel",
                "Scale normalization gives the canonical polarity kernel",
                PolarityFormula(),
                "Multiplying the center readout by delta squared over two yields zero on the "
                    + "unitary boundary and minus one in the hyperbolic bulk, exactly matching "
                    + "the selected one-point kernel.")),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Adelic/OffLineCurvatureDipole")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Quantum/FiniteDimensional")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/Pick/HermitianKernelNegativeSquares")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaLinear/Sylvester")),
        ]));

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Theorem);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula PowerTwo(Formula value) =>
        Seq(value, Caret, Grp(D(2)));

    private static Formula Frac(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

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

    private static Formula NormalizedFormula()
    {
        Formula delta = F.Id("delta");
        Formula tau = F.Id("tau");
        Formula numerator = Seq(PowerTwo(tau), Sp, Minus, Sp, PowerTwo(delta));
        Formula energy = Seq(PowerTwo(tau), Sp, Plus, Sp, PowerTwo(delta));
        Formula rhs = Seq(D(2), Sp, Cdot, Sp,
            Frac(Grp(numerator), Grp(PowerTwo(Grp(energy)))));
        return Disp(Seq(
            Forall, Sp, Typed(delta, Reals()), Comma, Sp,
            Typed(tau, Reals()), Comma, Sp,
            Call("normalizedCurvatureRayleighReadout", delta, tau),
            Sp, Eq, Sp, rhs, Dot));
    }

    private static Formula IntertwinerFormula()
    {
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula time = F.Id("t");
        return Disp(Seq(
            Forall, Sp, Typed(delta, Reals()), Comma, Sp,
            Typed(gamma, Reals()), Comma, Sp,
            Typed(time, Reals()), Comma, Sp,
            D(0), Sp, Lt, Sp, delta, Sp, Rightarrow, Sp,
            Call("offLineCurvature", delta, gamma, time), Sp, Eq, Sp,
            Call("normalizedCurvatureRayleighReadout", delta,
                Seq(time, Sp, Minus, Sp, gamma)), Dot));
    }

    private static Formula HyperbolicFormula()
    {
        Formula rho = F.Id("rho");
        Formula delta = Call("criticalDisplacement", rho);
        return Disp(Seq(
            Forall, Sp, Typed(rho, Complexes()), Comma, Sp,
            Call("IsHyperbolic", Call("offlineZeroMonodromy", rho)),
            Sp, Iff, Sp,
            Call("normalizedCurvatureRayleighReadout", delta, D(0)),
            Sp, Lt, Sp, D(0), Dot));
    }

    private static Formula UnitaryFormula()
    {
        Formula rho = F.Id("rho");
        Formula delta = Call("criticalDisplacement", rho);
        return Disp(Seq(
            Forall, Sp, Typed(rho, Complexes()), Comma, Sp,
            Call("IsUnitary", Call("offlineZeroCharacter", rho)),
            Sp, Iff, Sp,
            Call("normalizedCurvatureRayleighReadout", delta, D(0)),
            Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula PolarityFormula()
    {
        Formula delta = F.Id("delta");
        Formula lhs = Seq(
            Frac(PowerTwo(delta), D(2)), Sp, Cdot, Sp,
            Call("normalizedCurvatureRayleighReadout", delta, D(0)));
        Formula rhs = Call("polarityKernelValue", delta);
        return Disp(Seq(
            Forall, Sp, Typed(delta, Reals()), Comma, Sp,
            lhs, Sp, Eq, Sp, rhs, Dot));
    }
}
