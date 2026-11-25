using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletJointPositiveWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/CharacterSums/DirichletJointPositiveWindow.";
    private const string WindowSource = "https://github.com/the-omega-institute/riemann-hypothesis/blob/c7d25b3bfd7906388bb8eb0774e027a2b756a7b6/src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer chords certify the weighted positive mass of a signed Dirichlet ramp on a finite window.",
        H("Positive mass on Dirichlet ramp windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-ramp-positive-window-bounds"),
                DeclarationHandle.Create(Owner + "jointRamp_positive_window_bounds"),
                H("Two-sided bounds from the integer grid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nonprincipal complex Dirichlet character χ of nonzero modulus, "
                        + "let g = aU + b Re(gχ), with a ≥ 0 and b any real number. On 0 < Y < H, "
                        + "form the chords of g between Y, the interior integers, and H. Let Q be the sum "
                        + "of the integrals of the positive parts of those chords weighted by x^(−3/2). "
                        + "The weighted integral of max(g, 0) lies between Q and "
                        + "Q + (a/(4Y))(Y^(−1/2) − H^(−1/2)). The error is at most a/(4Y^(3/2)). "
                        + "In particular, the chord sum is exact when a = 0.")),
                    Paragraph(Text(
                        "The local ramp identities give coefficients Λ(n)(a + b Re χ(n)) for the "
                        + "finite Mangoldt sum. The linear coefficient is a(1 + γ) + b Re(L′(1,χ)/L(1,χ)), "
                        + "and the logarithmic term is −a x log x. Every Mangoldt summand is affine on a grid cell, "
                        + "regardless of its coefficient sign. Convexity of x log x and of "
                        + "x²/(2l) − x log x, with l the left endpoint, bound the gap above the chord "
                        + "by a(x − l)(u − x)/(2l) on [l,u]. Cell lengths are at most one. "
                        + "Taking positive parts preserves the lower bound and adds at most a/(8Y) "
                        + "before weighting. Integration telescopes the inverse-square-root terms. "
                        + "The nonprincipal assumption selects the logarithmic-derivative center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-ramp-subpower-windows-iff"),
                DeclarationHandle.Create(Owner + "jointRamp_subpower_windows_iff"),
                H("An equivalent test for arbitrarily late power windows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same g and δ > 0, the following conditions are equivalent. "
                        + "For every η > 0 and every cutoff Y₀ there is Y ≥ max(2,Y₀) such that "
                        + "the weighted positive integral on [Y,Y^(1+δ)] is ≤ Y^η. "
                        + "The same quantified assertion holds with Q in place of the integral.")),
                    Paragraph(Text(
                        "The finite lower bound transfers the same starting point from the integral "
                        + "to Q. In the reverse direction, apply the chord condition with η/2 and "
                        + "raise the cutoff until Y^(η/2) dominates both 2 and a/4. The finite "
                        + "upper bound then gives at most 2Y^(η/2) ≤ Y^η. The assumptions "
                        + "Y ≥ 2 and δ > 0 ensure a positive window length.")),
                    Paragraph(Text(
                        "The power-window quantifiers are inspired by Deduction.WindowHyp. "
                        + "The finite chord certificate and both implications are proved locally "
                        + "using the repository's ramp identities. " + WindowSource))),
                DescribeRole.Theorem))));
}
