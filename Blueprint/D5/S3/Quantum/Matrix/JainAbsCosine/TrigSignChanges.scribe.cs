using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.JainAbsCosine;

internal sealed class TrigSignChangesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trigonometric coefficients of absolute cosine Fourier modes.",
        H("Cosine bases and coefficient signs"), Blocks(
            Describe.Lean(DescribeId.Create("jain-cosine-base-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_bounds"),
                H("Positive bases below one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural m and l with 1 at most l at most m, the cosine of l times pi divided by 2m+1 lies strictly between zero and one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-cosine-base-order"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.cosine_base_strictAnti"),
                H("Strictly decreasing bases"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 at most a less than b at most m, the cosine base at b is strictly smaller than the base at a. The sample angles lie between zero and pi/2, where cosine is strictly decreasing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-logarithmic-exponent-order"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.logarithmic_exponent_order"),
                H("Ordered logarithmic exponents"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 at most a less than b at most m, the logarithm of the base at b is strictly smaller than the logarithm of the base at a, and the latter is strictly negative. These are the exponents of the real exponential sum representation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-mode-gap-sine-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.modeValue_sub"),
                H("The sine product expression for a mode gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m, j and d and every real r, the difference of modes j and j+d equals four times the sum, for l from one to m, of sin((2j+d)l theta) sin(dl theta) cos(l theta) raised to r. Here theta is pi/(2m+1). This follows from the difference of two cosines."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-short-gap-sine-positive"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_short_sine_pos"),
                H("Positivity of the short sine factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When d is one or two and 1 at most l at most m, sin(dl theta) is strictly positive. Thus this factor does not alter the sign of a gap coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-mode-coefficient-variations"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.mode_coefficients_signVariations"),
                H("Exactly j changes in mode coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 at most j at most m, the ordered list consisting of one followed by 2cos(2jl theta), for l from one through m, has exactly j sign variations. The order agrees with the strictly decreasing exponents zero, log cos(theta), through log cos(m theta)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-first-gap-phase-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_first_phase_bounds"),
                H("The first gap phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 1 at most j, d equal to one or two, and j+d at most m, the phase (2j+d)theta lies strictly between zero and pi. Its sine is therefore strictly positive, which determines the sign of the leading gap coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jain-gap-coefficient-variations"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges.gap_coefficients_signVariations"),
                H("Exactly j changes in short-gap coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If 1 at most j, d is one or two, and j+d at most m, the ordered list sin((2j+d)l theta) sin(dl theta), for l from one through m, has exactly j sign variations after zero entries are removed. A general arithmetic sampling argument labels nonzero samples by their open sine sign interval. Every interval from zero through j is represented, labels are nondecreasing, and consecutive interval labels have opposite signs. This includes composite odd orders and zero coefficients without a coprimality assumption."))), DescribeRole.Theorem))));
}
