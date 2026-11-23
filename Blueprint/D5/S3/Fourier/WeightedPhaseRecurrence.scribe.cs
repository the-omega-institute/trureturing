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
                + "and let ε, δ, a, and R be real with ε > 1/N, δ > 0, and R > 0. "
                + "For integer vectors k set ξ(k) = Σⱼ kⱼgⱼ and φ(k) = Σⱼ kⱼθⱼ. "
                + "For every k with |kⱼ| ≤ N in every coordinate, assume cos φ(k) = 1 "
                + "if ξ(k) = 0 and |ξ(k)| ≥ δ if ξ(k) ≠ 0.")),
            Describe.Lean(
                DescribeId.Create("normalized-phase-loss"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRecurrence.phaseLoss"),
                H("Weighted phase loss"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, F.Id("t"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Quad,
                    Equal(Call("phaseLoss", F.Id("g"), Theta, F.Id("p"), F.Id("t")), Loss())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition applies to arbitrary real weights. The recurrence theorem "
                    + "uses nonnegativity and normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-phase-recurrence"),
                DeclarationHandle.Create("D5/S3/Fourier/WeightedPhaseRecurrence.weighted_phase_recurrence"),
                H("A window uniform in its starting time"),
                StatementSource.FromAuthor(WindowStatement()),
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
                        + "(pⱼ/N) cos(Nxⱼ) times the product of F_N over the other coordinates. "
                        + "In each summand the two modes at ±N have coefficient 1/2 in coordinate j. "
                        + "Multiplication of the complex characters and taking real parts gives "
                        + "a cosine expansion on the integer box. All coefficients are nonnegative. "
                        + "The coefficient at the zero index is ε − 1/N, and evaluating with all "
                        + "offsets zero gives total coefficient mass εN^|J|.")),
                    Paragraph(Text(
                        "The zero index contributes R(ε − 1/N) to the integral. Other exact "
                        + "resonances contribute nonnegatively by phase compatibility. For a nonzero "
                        + "frequency ξ, the affine cosine integral is a difference of two sines "
                        + "divided by ξ and has absolute value at most 2/|ξ| ≤ 2/δ. "
                        + "The length inequality gives a strictly positive integral. At a time "
                        + "where the integrand is positive, P is nonnegative and the loss is "
                        + "strictly below ε.")),
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
        return Seq(Subscript(Sum, Seq(j, InMacro, F.Id("J"))), Thin,
            Subscript(F.Id("p"), j), Seq(Open, Subtract(D(1), Call("cos", angle)), Close));
    }

    private static Formula WindowStatement()
    {
        var n = F.Id("N");
        var a = F.Id("a");
        var r = F.Id("R");
        var t = F.Id("t");
        var origin = Subtract(Varepsilon, new Formula.Fraction(D(1), n));
        var mass = Seq(Varepsilon, new Formula.Power(n, Seq(Vert, F.Id("J"), Vert)));
        return Disp(Seq(r, DeltaLower, Open, origin, Close, Gt,
            D(2), Open, Subtract(mass, Seq(Open, origin, Close)), Close,
            Quad, Longrightarrow, Quad, Exists, t, InMacro,
            OpenBracket, a, Comma, Add(a, r), CloseBracket, Comma, Quad, Loss(), Lt, Varepsilon));
    }
}
