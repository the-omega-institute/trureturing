using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusDyadicBoundaryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary";
    private const string Parseval = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicUnitWeightParseval";
    private const string LineFourier = "D5/S3/Weil/ZetaGamma/FormCore/LineFourier";
    private const string PartialSum = "D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence";
    private const string DyadicEnergy = "D5/S3/Weil/Mertens/MobiusDyadicEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted signed dyadic Möbius energy controls the reciprocal of zeta on a vertical line.",
        H("Weighted Möbius energy and the boundary reciprocal of zeta"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-reciprocal-zeta-square-bound"),
                DeclarationHandle.Create(Owner + ".weighted_reciprocal_zeta_sq_bound_of_mobiusDyadicEnergy"),
                H("Square-integrability of the weighted reciprocal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the actual signed difference D(x) = S(x) − S(2x), where S(x) is the finite "
                        + "sum of μ(n)/n over positive integers n ≤ x. Fix 0 ≤ θ < 2 with θ ≠ 1 "
                        + "and assume that ζ has no zeros on the line of real part θ. If the integral "
                        + "of D(x)² x⁻⁽²θ⁻¹⁾ over x > 1 is finite, the theorem bounds the whole-line "
                        + "integral of 1/((1+|y|)² |ζ(θ+iy)|²) by the displayed expression.")),
                    Paragraph(Text(
                        "The change of variables x = exp u gives a causal function in L². "
                        + "Damping it by exp(−hu) yields L¹ and L² and preserves the L² bound. "
                        + "Multiply the dyadic Mellin identity by the pole-removed zeta factor "
                        + "before using holomorphic uniqueness. Local division at each point "
                        + "of the zero-free line gives convergence of the angular Fourier transforms. "
                        + "Apply Plancherel and Fatou to bound the limiting symbol, and then use "
                        + "|1−2ˢ| ≥ |1−2ᶿ⁻¹| and |s| ≤ 1+|y| for s = θ−1+iy.")),
                    Paragraph(Text(
                        "When the real parts of the nontrivial zeros have an unattained supremum "
                        + "Θ < 1, the theorem applies at θ = Θ. In this case finite critical "
                        + "Möbius energy forces finite weighted reciprocal mass on the zero-abscissa line."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Parseval)),
            DocumentEdge.Dependency.Create(GidRef.Create(LineFourier)),
            DocumentEdge.Dependency.Create(GidRef.Create(PartialSum)),
            DocumentEdge.Dependency.Create(GidRef.Create(DyadicEnergy))
        ]));
}
