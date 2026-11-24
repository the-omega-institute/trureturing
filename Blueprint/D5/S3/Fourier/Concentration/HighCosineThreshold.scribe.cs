using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class HighCosineThresholdDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/HighCosineThreshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-level probability law minimizes squared mass for high joint cosine thresholds.",
        H("The high-threshold minimum for two cosine moments"),
        Blocks(
            Paragraph(Text(
                "Write c for a finite real readout and use 2c² − 1 as the second readout. "
                + "The top value is one and occurs once. The remaining values lie between "
                + "the attained levels ℓ and u. Write g(x) = x − (2x² − 1), "
                + "p = −g(ℓ)/(g(u) − g(ℓ)), b = pu + (1−p)ℓ and r = (1−a)/(1−b). "
                + "The law gives mass 1−r to the top index, rp to the level u, and r(1−p) to "
                + "the level ℓ. Each level’s mass is divided equally among its indices.")),
            Describe.Lean(
                DescribeId.Create("finite-readout-threshold-certificate"),
                DeclarationHandle.Create(Owner + ".high_threshold_certificate"),
                H("A finite interpolation certificate"),
                StatementSource.FromAuthor(FiniteStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three levels satisfy ℓ < u < 1, u + ℓ < 0 and g(ℓ) < 0 < g(u). "
                    + "Interpolate the three weights by a quadratic P with moment coefficients β "
                    + "and γ in the basis 1, x, 2x² − 1. For each of β, γ and the values −P(x) at "
                    + "intermediate levels, take the slope 1 − f(1)/f(0) as a function of r. "
                    + "Let B be the maximum of those slopes and one. At thresholds a in "
                    + "[1 − (1−b)/B, 1] the two moments equal a. The squared mass is "
                    + "(1−r)² + r²(p²/nᵤ + (1−p)²/nₗ), where nᵤ and nₗ are level counts. "
                    + "The excess squared mass of any feasible law bounds its squared distance "
                    + "from the candidate, which gives uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-descent-below-cutoff"),
                DeclarationHandle.Create(Owner + ".exists_smaller_energy_below_threshold"),
                H("A feasible descent below the cutoff"),
                StatementSource.FromAuthor(DescentStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When b < a is below the cutoff, all three supporting levels have positive "
                    + "weight. If a moment coefficient is negative, a perturbation within the "
                    + "support increases that moment and preserves the other. If an intermediate "
                    + "value of P is positive, a perturbation adds weight there and uses the "
                    + "three support levels to preserve both moments. A sufficiently small "
                    + "positive step decreases the squared mass in either case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-high-threshold-certificate"),
                DeclarationHandle.Create(Owner + ".cyclic_high_threshold_certificate"),
                H("The sharp high-threshold interval on a cycle"),
                StatementSource.FromAuthor(CyclicStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For q at least four use c(k) = cos(2πk/q) on its canonical residue "
                    + "representatives. The first off-center maximum occurs at k = 1, and a "
                    + "minimum occurs at the integer part of q/2. Reflecting angles into "
                    + "[0, π] proves the required level order and strict signs. The cutoff lies "
                    + "strictly between b and one. The law minimizes squared mass from the "
                    + "cutoff through one, and a feasible law has smaller squared mass "
                    + "at each threshold strictly between b and the cutoff."))),
                DescribeRole.Theorem))));

    private static Formula Cutoff => new Formula.Subscript(F.Id("a"), F.Id("crit"));

    private static Formula CertifiedInterval() =>
        Seq(Forall, Sp, F.Id("a"), Sp, InMacro, Sp, OpenBracket, Cutoff, Comma, D(1),
            CloseBracket, Comma, Sp, Operatorname, Grp(F.Id("Certified")), Open, F.Id("a"), Close);

    private static Formula Descent() =>
        Seq(Forall, Sp, F.Id("a"), Sp, InMacro, Sp, Open, F.Id("b"), Comma, Cutoff, Close,
            Comma, Sp, Exists, Sp, F.Id("w"), Comma, Sp, Operatorname, Grp(F.Id("Feasible")),
            Open, F.Id("w"), Comma, F.Id("a"), Close, Sp, Land, Sp, F.Id("E"), Open, F.Id("w"),
            Close, Lt, F.Id("E"), Open, new Formula.Subscript(F.Id("v"), F.Id("a")), Close);

    private static Formula FiniteStatement() =>
        Disp(Seq(Cutoff, Lt, D(1), Sp, Land, Sp, Open, CertifiedInterval(), Close));

    private static Formula DescentStatement() => Disp(Descent());

    private static Formula CyclicStatement() =>
        Disp(new Formula.Aligned([
            Seq(Amp, F.Id("q"), Ge, D(4), Sp, Longrightarrow, Sp, F.Id("b"), Lt, Cutoff, Lt, D(1), Comma),
            Seq(Amp, CertifiedInterval(), Comma),
            Seq(Amp, Descent())
        ]));
}
