using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class ReflectedZeroModePhaseFlatteningDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaLinear/ReflectedZeroModePhaseFlattening.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate normalized zero modes into radial and phase channels.",
        H("Reflected Zero Modes and Phase Flattening"),
        Blocks(
            DefinitionNode(
                "critical-displacement",
                "criticalDisplacement",
                "Signed displacement from the critical line",
                "The displacement is the real part of the spectral point minus the frozen "
                    + "critical abscissa."),
            DefinitionNode(
                "normalized-zero-generator",
                "normalizedZeroGenerator",
                "Normalized zero generator",
                "After the uniform damping shift cancels, the generator has real part minus "
                    + "the critical displacement and imaginary part equal to the ordinate."),
            DefinitionNode(
                "normalized-zero-mode",
                "normalizedZeroMode",
                "Normalized zero mode",
                "The auxiliary mode is the complex exponential of the normalized generator "
                    + "times a real mode parameter."),
            DefinitionNode(
                "phase-flattened-zero-mode",
                "phaseFlattenedZeroMode",
                "Phase-flattened zero mode",
                "Multiplication by the inverse ordinate phase removes the common unit-modulus "
                    + "rotation while retaining the radial channel."),
            TheoremNode(
                "normalized-generator-skew-criterion",
                "normalized_zero_generator_skew_iff_critical_line",
                "Skewness is exactly critical-line location",
                SkewFormula(),
                "The normalized generator is skew under complex conjugation exactly when its "
                    + "real part vanishes, which is exactly critical-line location."),
            TheoremNode(
                "normalized-mode-factorization",
                "normalized_zero_mode_factorization",
                "The zero mode factors into radial and phase channels",
                FactorizationFormula(),
                "The radial factor carries the horizontal displacement and the phase factor "
                    + "carries the ordinate. The phase factor has unit norm in a separate Lean "
                    + "theorem."),
            TheoremNode(
                "phase-flattening-identity",
                "phase_flattened_zero_mode_eq_radial",
                "Phase flattening leaves the radial mode",
                FlatteningFormula(),
                "The inverse phase exactly cancels the common ordinate rotation, with no "
                    + "approximation or branch choice."),
            TheoremNode(
                "functional-reflection-time-reversal",
                "zero_mode_functional_reflection_time_reversal",
                "Functional reflection acts as mode-time reversal",
                FunctionalReflectionFormula(),
                "The map rho to one minus rho negates both generator coordinates. On the "
                    + "auxiliary exponential mode this equals reversing the mode parameter."),
            TheoremNode(
                "conjugation-frequency-reversal",
                "zero_mode_conjugation",
                "Conjugation reverses the frequency channel",
                ConjugationFormula(),
                "Complex conjugation preserves the radial rate and reverses the ordinate phase. "
                    + "It is distinct from functional reflection and from same-height mirror."),
            TheoremNode(
                "same-height-mirror-reciprocity",
                "phase_flattened_critical_line_mirror_reciprocal",
                "Same-height mirror gives reciprocal radial branches",
                MirrorReciprocityFormula(),
                "After phase flattening, rho and one minus conjugate rho have opposite radial "
                    + "rates, so their two modes multiply to one."),
            TheoremNode(
                "zero-data-symmetry-commutation",
                "zeroData_reflection_conjugation_commute",
                "Stored reflection and conjugation commute",
                SymmetryCommutationFormula(),
                "Duplicate-free zero enumeration turns equality of the two same-height mirror "
                    + "images into equality of the two index permutations.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaLinear/CriticalDampingGenerator")),
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

    private static Formula SkewFormula()
    {
        Formula rho = F.Id("rho");
        Formula generator = Call("normalizedZeroGenerator", rho);
        return Disp(Seq(
            Call("conj", generator), Sp, Eq, Sp, Minus, generator,
            Sp, Iff, Sp,
            Call("Re", rho), Sp, Eq, Sp, F.Id("criticalAbscissa"), Dot));
    }

    private static Formula FactorizationFormula()
    {
        Formula rho = F.Id("rho");
        Formula time = F.Id("t");
        return Disp(Seq(
            Call("normalizedZeroMode", rho, time), Sp, Eq, Sp,
            Call("radialZeroMode", rho, time), Sp, Cdot, Sp,
            Call("commonZeroPhase", rho, time), Dot));
    }

    private static Formula FlatteningFormula()
    {
        Formula rho = F.Id("rho");
        Formula time = F.Id("t");
        return Disp(Seq(
            Call("phaseFlattenedZeroMode", rho, time), Sp, Eq, Sp,
            Call("radialZeroMode", rho, time), Dot));
    }

    private static Formula FunctionalReflectionFormula()
    {
        Formula rho = F.Id("rho");
        Formula time = F.Id("t");
        return Disp(Seq(
            Call("normalizedZeroMode", Call("functionalReflection", rho), time),
            Sp, Eq, Sp,
            Call("normalizedZeroMode", rho, Seq(Minus, time)), Dot));
    }

    private static Formula ConjugationFormula()
    {
        Formula rho = F.Id("rho");
        Formula time = F.Id("t");
        return Disp(Seq(
            Call("normalizedZeroMode", Call("conj", rho), time),
            Sp, Eq, Sp,
            Call("conj", Call("normalizedZeroMode", rho, time)), Dot));
    }

    private static Formula MirrorReciprocityFormula()
    {
        Formula rho = F.Id("rho");
        Formula time = F.Id("t");
        return Disp(Seq(
            Call("phaseFlattenedZeroMode", rho, time), Sp, Cdot, Sp,
            Call("phaseFlattenedZeroMode", Call("criticalLineMirror", rho), time),
            Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula SymmetryCommutationFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(
            Call("reflection", Call("conjugation", n)), Sp, Eq, Sp,
            Call("conjugation", Call("reflection", n)), Dot));
    }
}
