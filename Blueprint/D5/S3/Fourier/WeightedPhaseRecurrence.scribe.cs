using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class WeightedPhaseRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Fejer product gives finite interval recurrence for normalized weighted phase loss.",
        H("Weighted Phase Recurrence on a Finite Interval"),
        Blocks(
            Paragraph(Text(
                "Let J be a finite index type, and let g, θ, and p be real-valued families on J. "
                + "The entries of p are nonnegative and sum to one. Let N be a positive integer "
                + "and let ε > 1/N. For each integer vector k in the box |kⱼ| ≤ N set "
                + "ξ(k) = Σⱼ kⱼgⱼ and φ(k) = Σⱼ kⱼθⱼ.")),
            Describe.Lean(
                DescribeId.Create("normalized-phase-loss"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRecurrence.phaseLoss"),
                H("Weighted phase loss"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Quad,
                    Equal(Call("phaseLoss", F.Id("g"), Theta, F.Id("p"), F.Id("t")), Loss())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition applies to arbitrary real weights. The recurrence "
                    + "theorems use nonnegativity and normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("recurrence-margin"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRecurrence.recurrenceMargin"),
                H("Signed Fejér margin"),
                StatementSource.FromAuthor(Disp(Equal(Margin(),
                    Subtract(Multiply(F.Id("R"), F.Id("A")), Call("B", F.Id("R")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For offsets xⱼ = gⱼt − θⱼ, take the product P = ∏ⱼ F_N(xⱼ) of "
                        + "the Fejér polynomials. Each F_N is the normalized squared modulus of "
                        + "the geometric exponential sum of length N. Its triangular coefficients "
                        + "are 1 − |k|/N for |k| ≤ N, with the two endpoints zero. The one-coordinate "
                        + "identity (1 − cos x)F_N(x) = (1 − cos(Nx))/N follows from the "
                        + "geometric-sum identity.")),
                    Paragraph(Text(
                        "Expand (ε − phaseLoss)P as (ε − 1/N)P plus the sum over j of "
                        + "(pⱼ/N) (F_N(xⱼ) − 1 + cos(Nxⱼ)) times the product of F_N over "
                        + "the other coordinates. Subtracting 1 removes the constant mode of "
                        + "the triangular coefficients in coordinate j. The cosine adds the "
                        + "two modes at ±N with coefficient 1/2 each. Multiplying the complex "
                        + "characters and taking real parts gives "
                        + "a cosine expansion on the integer box with coefficients cₖ. "
                        + "All coefficients are nonnegative under the stated hypotheses.")),
                    Paragraph(Text(
                        "The signed sum A adds cₖ cos φ(k) over the indices with ξ(k) = 0. "
                        + "The penalty B(R) adds 2cₖ |sin(Rξ(k)/2)|/|ξ(k)| over the "
                        + "remaining indices. The definition is a finite sum for arbitrary "
                        + "real inputs and natural N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-phase-recurrence-of-margin"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/WeightedPhaseRecurrence.weighted_phase_recurrence_of_margin"),
                H("Quantitative loss in every window"),
                StatementSource.FromAuthor(MarginStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At zero frequency the integral of the cosine is R cos φ(k). "
                    + "At nonzero frequency the sine difference identity gives the integral "
                    + "as 2 sin(Rξ(k)/2) cos(ξ(k)(a+R/2) − φ(k))/ξ(k). "
                    + "Nonnegative coefficients then bound the integral of (ε − phaseLoss)P "
                    + "below by the margin. The maximum on the closed interval is at least "
                    + "the margin divided by R. Each Fejér factor lies between zero and N, "
                    + "so at that maximum, ε − phaseLoss is at least the margin divided by RN^|J|. "
                    + "A positive margin gives strict loss below ε."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-phase-recurrence"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRecurrence.weighted_phase_recurrence"),
                H("A window from a common frequency gap"),
                StatementSource.FromAuthor(WindowStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let δ > 0. For each index in the box, assume cos φ(k) = 1 "
                        + "if ξ(k) = 0 and |ξ(k)| ≥ δ if ξ(k) ≠ 0. "
                        + "The zero coefficient is ε − 1/N, and evaluating at zero offsets "
                        + "gives total coefficient mass εN^|J|. The length inequality forces "
                        + "R > 0 since the total mass is at least the zero coefficient. "
                        + "Compatibility gives A ≥ ε − 1/N. The nonzero-frequency indices exclude "
                        + "the zero index and each incurs at most 2cₖ/δ, so "
                        + "B(R) ≤ 2(εN^|J| − (ε − 1/N))/δ. The margin is positive by the length "
                        + "inequality, and the quantitative loss bound gives the strict conclusion.")),
                    Paragraph(Text(
                        "This uses the Fejér product of Bohr and Jessen and the finite averaging "
                        + "mechanism discussed by Sourmelidis (arXiv:2411.14221, §4). The "
                        + "finite exponential average also appears as norm_avg_le in the "
                        + "Riemann hypothesis repository's ExpSumCoeffEqZeroOfVanishing.lean "
                        + "at b8864ecd5798c6030a03d756fab95f0b89a12754, in the cycles-per-unit "
                        + "convention. Here the frequencies are angular and the interval "
                        + "start is arbitrary.")),
                    Paragraph(Text(
                        "Maksimova (arXiv:2405.07051, Theorem 1) and Gonek–Montgomery "
                        + "(DOI 10.1016/j.indag.2016.02.002, Theorem C as quoted there) assume "
                        + "separation from zero for every nonzero vector in their respective "
                        + "boxes and allow arbitrary targets with coordinatewise tolerances. "
                        + "The weighted loss bound here permits exact resonances in its box "
                        + "when the target character on each is one. Sourmelidis also notes "
                        + "that Chen (DOI 10.1112/S0024610700008772) treats linear dependencies. "
                        + "For example, with g = (1,3), θ = (0,π), N = 2, and δ = 1, "
                        + "the only in-box relation is zero, and the relation (3,−1) "
                        + "outside the box has target cosine −1.")),
                    Paragraph(Text("For the qualitative comparison, "),
                        Ref("D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit"),
                        Text(
                            " imposes the same character test on the whole relation lattice "
                            + "to obtain orbit closure on each upper ray. The cosine of the "
                            + "sum is the real part of the corresponding circle character "
                            + "and equals one exactly when that character is one. The product "
                            + "in the finite argument retains the frequencies in the stated box. "
                            + "With all θⱼ = π/2, cos(gⱼt − θⱼ) = sin(gⱼt) and the target "
                            + "character of k is i raised to Σⱼkⱼ. Its being one is the "
                            + "sum-divisibility condition in "),
                        Ref("D5/S3/Fourier/ShortPhaseRelations"),
                        Text(
                            " restricted here to the box and applied to the normalized "
                            + "pointwise sine loss. For a fixed zeta cutoff the window theorem "
                            + "requires the stated compatibility and a verified separation δ."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula basis, Formula index) =>
        Seq(basis, Underscore, Grp(index));

    private static Formula Loss()
    {
        var j = F.Id("j");
        var angle = Subtract(Seq(Subscript(F.Id("g"), j), F.Id("t")), Subscript(Theta, j));
        return Seq(Subscript(Sum, Seq(j, InMacro, Sp, F.Id("J"))), Thin,
            Subscript(F.Id("p"), j), Seq(Open, Subtract(D(1), Call("cos", angle)), Close));
    }

    private static Formula Margin() =>
        Call("recurrenceMargin", F.Id("g"), Theta, F.Id("p"), F.Id("N"), Varepsilon, F.Id("R"));

    private static Formula BoxScale() => new Formula.Power(F.Id("N"), Seq(Bar, F.Id("J"), Bar));

    private static Formula WindowTime() =>
        Seq(Exists, Sp, F.Id("t"), InMacro, OpenBracket, F.Id("a"), Comma,
            Add(F.Id("a"), F.Id("R")), CloseBracket, Comma, Quad);

    private static Formula MarginStatement()
    {
        var r = F.Id("R");
        return Disp(Seq(r, Gt, D(0), Comma, Quad, Margin(), Gt, D(0),
            Quad, Longrightarrow, Quad, WindowTime(),
            AtMost(Loss(), Subtract(Varepsilon, new Formula.Fraction(Margin(), Multiply(r, BoxScale()))))));
    }

    private static Formula WindowStatement()
    {
        var n = F.Id("N");
        var r = F.Id("R");
        var origin = Subtract(Varepsilon, new Formula.Fraction(D(1), n));
        var mass = Multiply(Varepsilon, BoxScale());
        return Disp(Seq(r, DeltaLower, Open, origin, Close, Gt,
            D(2), Open, Subtract(mass, Seq(Open, origin, Close)), Close,
            Quad, Longrightarrow, Quad, WindowTime(), Loss(), Lt, Varepsilon));
    }
}
