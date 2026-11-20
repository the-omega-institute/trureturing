using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusDyadicBoundaryWindowsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundaryWindows";
    private const string Boundary = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary";
    private const string DyadicEnergy = "D5/S3/Weil/Mertens/MobiusDyadicEnergy";
    private const string KappaGap = "D5/S3/Arith/Robin/ForwardKernel/KappaGap";
    private const string HalfStripZero = "D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical signed dyadic Möbius energy bounds the sum of contributions from disjoint zero windows.",
        H("Disjoint zero windows at the zero abscissa"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-reciprocal-window-mass"),
                DeclarationHandle.Create(Owner + ".finite_gap_mass_le_integral_reciprocalDensity"),
                H("A reciprocal mass bound on a zero-free line"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    SumContributions(F.Seq(F.Id("i"), F.InMacro, F.Sp, F.Id("t"))),
                    F.Leq, F.Int, F.Underscore, F.Grp(F.Mathbb, F.Grp(F.Id("R"))), F.Thin,
                    F.Id("g"), F.Open, F.Id("y"), F.Close, F.Thin,
                    F.Mathrm, F.Grp(F.Id("d")), F.Id("y")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let f have no zeros on the vertical line of real part θ. Define the density "
                    + "g(y) = 1/((1+|y|)² |f(θ+iy)|²) and assume it is integrable. For a finite "
                    + "family of zeros ρᵢ of f, take gaps δᵢ = θ − Re ρᵢ in (0, 1] and pairwise "
                    + "disjoint open ordinate windows of radius δᵢ. Suppose f is complex "
                    + "differentiable with derivative norm at most Mᵢ > 0 on the closed rectangle "
                    + "between ρᵢ and its window on the line. Integrating the pointwise lower "
                    + "bound on each window gives a contribution aᵢ = 1/(8δᵢMᵢ²(1+|Im ρᵢ|)²). "
                    + "Disjointness lets the integrals add within the total mass of g."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-zero-window-mass"),
                DeclarationHandle.Create(Owner + ".finite_gap_mass_le_of_critical_energy"),
                H("Finite families of disjoint windows"),
                StatementSource.FromAuthor(F.Disp(Bound(F.Seq(F.Id("i"), F.InMacro, F.Sp, F.Id("t"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let θ < 1 be the unattained supremum of the real parts of nontrivial zeta zeros. "
                        + "For each zero ρ = β + iγ, write δ = θ − β. Use the open ordinate interval "
                        + "(γ − δ, γ + δ) and choose M > 0 that bounds the norm of the zeta derivative "
                        + "on the corresponding closed rectangle between real parts β and θ. "
                        + "Write S(x) for the sum of μ(n)/n over positive integers n ≤ x "
                        + "and D(x) = S(x) − S(2x). Assume D(x)² x^(1−2θ) is integrable over "
                        + "x > 1 and write E for its integral.")),
                    Paragraph(Text(
                        "Along the segment from ρ to θ + iy the derivative bound gives "
                        + "|ζ(θ + iy)| ≤ 2δM for y in that interval. The weight satisfies "
                        + "1 + |y| ≤ 2(1 + |γ|). Integrating the reciprocal density over the "
                        + "length 2δ gives a lower bound of 1/(8δM²(1 + |γ|)²), denoted by aᵢ. "
                        + "Pairwise disjoint intervals let these bounds add within the total mass "
                        + "controlled by the critical Möbius energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("summable-zero-window-mass"),
                DeclarationHandle.Create(Owner + ".gap_mass_summable_of_critical_energy"),
                H("Summability of the window contributions"),
                StatementSource.FromAuthor(F.Disp(Bound(F.Id("i")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same zero-abscissa, derivative and weighted square-integrability "
                    + "hypotheses, assume the open windows are pairwise disjoint throughout "
                    + "the family. The finite-family theorem bounds every finite sum of "
                    + "nonnegative contributions. The full family is summable and its sum "
                    + "satisfies the displayed bound."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary)),
            DocumentEdge.Dependency.Create(GidRef.Create(DyadicEnergy)),
            DocumentEdge.Dependency.Create(GidRef.Create(KappaGap)),
            DocumentEdge.Dependency.Create(GidRef.Create(HalfStripZero))
        ]));

    private static Formula Bound(Formula index)
    {
        var weight = F.Seq(F.Open, F.D(1), F.Minus, F.D(2), F.Caret,
            F.Grp(F.Theta, F.Minus, F.D(1)), F.Close, F.Caret, F.Grp(F.D(2)));
        return F.Seq(
            SumContributions(index), F.Leq, F.D(4), F.Plus, F.Frac, F.Grp(F.D(4), F.Pi, F.Sp, F.Id("E")), F.Grp(weight));
    }

    private static Formula SumContributions(Formula index)
        => F.Seq(F.Sum, F.Underscore, F.Grp(index), F.Thin, F.Id("a"), F.Underscore, F.Grp(F.Id("i")));
}
