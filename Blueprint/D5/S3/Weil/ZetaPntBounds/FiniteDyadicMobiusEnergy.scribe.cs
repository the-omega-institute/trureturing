using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class FiniteDyadicMobiusEnergyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/FiniteDyadicMobiusEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dyadic Möbius energy and the Riemann hypothesis",
        H("Finite dyadic Möbius energy and the Riemann hypothesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("banded-energy-identity"),
                DeclarationHandle.Create(Owner + ".energy_eq_banded_sum"),
                H("The finite banded identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each natural cutoff P, set a(n) = μ(n)/n in the rationals and "
                        + "let d(j) be the sum of a(n) over j/2 < n ≤ j, with j/2 rounded down. "
                        + "The energy E(P) is the sum of d(j)² over 1 ≤ j < P.")),
                    Paragraph(Text(
                        "Expanding the squares gives a double sum over 1 ≤ m,n < P of "
                        + "a(m)a(n) times the number of cells containing both m and n. "
                        + "These cells are exactly the integers from max(m,n), inclusive, "
                        + "to min(P,2 min(m,n)), exclusive. Their number is the truncated "
                        + "natural difference of those endpoints. In particular the weight "
                        + "vanishes when 2 min(m,n) ≤ max(m,n).")),
                    Paragraph(Text(
                        "On the unit cell with left endpoint j, the real reciprocal Möbius "
                        + "shell equals d(j). Its absolute integral from 1 to an integer "
                        + "P ≥ 1 is therefore the sum of |d(j)|. By Cauchy–Schwarz its square "
                        + "is at most (P − 1)E(P)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cofinal-real-energy"),
                DeclarationHandle.Create(Owner + ".riemannHypothesis_iff_cofinal_energy"),
                H("The real exponent criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Riemann hypothesis is equivalent to the following statement. "
                        + "For every real ε > 0 and every natural threshold N, there is "
                        + "a natural P ≥ N for which the real coercion of E(P) is at most P^ε.")),
                    Paragraph(Text(
                        "Under RH, the zero-free half-plane bounds the ordinary Möbius prefix "
                        + "by a constant times N^(1/2+δ) for any positive δ. Finite Abel "
                        + "summation gives a bound of order j^(δ−1/2) on |d(j)|. Summing the "
                        + "squares gives order P^(2δ), so choosing 2δ < ε absorbs the constant "
                        + "for all sufficiently large P.")),
                    Paragraph(Text(
                        "Conversely, a zero with real part β > 1/2 in the critical strip gives "
                        + "a positive lower bound of order P^β on one plus the absolute shell "
                        + "mass at every cutoff P ≥ 1. At the cofinal cutoffs with "
                        + "ε = β − 1/2, Cauchy–Schwarz gives an upper exponent (1+ε)/2 < β. "
                        + "This excludes such a zero. The zeta functional equation excludes "
                        + "zeros in the left half of the strip by reflection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cofinal-rational-energy-power"),
                DeclarationHandle.Create(Owner + ".riemannHypothesis_iff_cofinal_energy_pow"),
                H("The rational power criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Riemann hypothesis holds exactly when for every positive natural "
                        + "k and every natural threshold N, there is a natural P ≥ N with "
                        + "E(P)^k ≤ P in the rationals. Each fixed-cutoff inequality uses "
                        + "finite rational sums and an integer power.")),
                    Paragraph(Text(
                        "Taking ε = 1/k in the real criterion and raising the nonnegative "
                        + "sides to the kth power gives the rational inequality. For the "
                        + "reverse implication choose k with 1/k ≤ ε and use threshold "
                        + "max(N,1). Taking the kth root bounds E(P) by P^(1/k) ≤ P^ε."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusDyadicShell")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaPntBounds/MobiusShortAverage"))
        ]));
}
