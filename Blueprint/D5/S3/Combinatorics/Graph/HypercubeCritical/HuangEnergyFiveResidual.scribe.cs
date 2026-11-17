using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class HuangEnergyFiveResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangEnergyFiveResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer energy-five Huang residuals are unit vectors of support thirty or coherent signed path Laplacians.",
        H("Full classification of energy-five residuals"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4. The original 258-vertex question and literature "
                    + "novelty remain unresolved. Here intA and intCoeff retain the "
                    + "original signed FALSE-prefix Huang integer operator and "
                    + "coefficients from HuangIntegralNormGap; L = 3I − A.")),
            Describe.Lean(
                DescribeId.Create("huang-energy-five-residual-invariants"),
                DeclarationHandle.Create(Prefix + "energy_five_residual_invariants"),
                H("Energy five fixes bounds and both parity norms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary f : Q9 → ℤ, the single hypothesis "
                            + "HuangIntegralNormGap.energy f = 5 implies that every "
                            + "Lf coordinate lies in [−2,2], the sum of (Lf x)² "
                            + "is thirty, and the squared norms of evenPart (Lf) "
                            + "and oddPart (Lf) are each fifteen. No cut hypothesis "
                            + "is required. The Laplacian norm identity and its "
                            + "−3 eigenvector parity identities give the norms; "
                            + "the integral energy bound gives the coordinate range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("huang-energy-five-unit-support"),
                DeclarationHandle.Create(Prefix + "energy_five_unit_support"),
                H("A unit energy-five residual has exactly thirty support points"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For f : Q9 → ℤ with HuangIntegralNormGap.energy f = 5, "
                            + "if every Lf coordinate is 0, 1, or −1, then "
                            + "(Finset.univ.filter (fun x => Lf x ≠ 0)).card = 30. "
                            + "For unit coordinates, squared norm equals actual "
                            + "support cardinality, so the preceding invariant "
                            + "proves the conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("huang-energy-five-residual-classification"),
                DeclarationHandle.Create(Prefix + "classify_energy_five_residual"),
                H("Either unit support thirty or a coherent signed three-vertex path Laplacian"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary integer f on Q9 with energy five, either "
                            + "Lf is unit-valued with actual support cardinality "
                            + "thirty, or there exist y,z,w : Q9 and s : ℤ with "
                            + "s² = 1, actual cube adjacency y ∼ z and y ∼ w, and "
                            + "z ≠ w, such that Lf = Lg, where "
                            + "g(x) = s δ_y(x) + s intCoeff y z δ_z(x) "
                            + "+ s intCoeff y w δ_w(x). This is a coherent signed "
                            + "three-vertex path Laplacian; it does not assert "
                            + "f = g or that f itself has three-point support.")),
                    Paragraph(Text(
                        "If Lf is nonunit, choose a parity half containing a "
                            + "coefficient of magnitude two. Its squared norm is "
                            + "fifteen and its coordinates are 0, ±1, or ±2, so "
                            + "its support has at most twelve points. The actual "
                            + "parity stopping-set classification CubeTwelveSupport "
                            + "makes it a nine-point star with exactly two heavy "
                            + "leaves. The minimal-residual classification and "
                            + "eigenvector recovery from one parity half identify "
                            + "the displayed P3 Laplacian.")),
                    Paragraph(Text(
                        "This classification neither excludes unit support thirty "
                            + "nor excludes P3 residuals for unrestricted f. It does "
                            + "not exclude the original 258-vertex candidates or "
                            + "assert that every energy-five residual is unit."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFourCut"))
        ]));
}
