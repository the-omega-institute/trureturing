using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class QubitQutritAnchorConvexityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/qian2026complementarycorrelations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Anchor convexity for faithful qubit–qutrit product states.",
        H("Anchor convexity for faithful qubit–qutrit product states"),
        Blocks(
            Paragraph(Text("Qian arXiv:2608.14806v2, Lemma 7.1, equation (39), and Definition 7.2 specify the faithful-product quadratic form. Section 11(1) asks separately for its nonnegativity in dimensions two and three and for the full complementary quantum correlations inequality. Proposition 7.6 covers the case where either marginal is diagonal in either of its measured bases. The earlier sharp two-ray discrimination bound S ≤ 8/3 appears in the separate candidate release DOI 10.5281/zenodo.23933731 and has an orthogonal two-ray state restriction. The full qubit–qutrit complementary-correlation inequality remains open.")),
            Describe.Lean(DescribeId.Create("qian-qubitqutritanchorconvexity-qubit-qutrit-anchor-convexity"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity.qubit_qutrit_anchor_convexity"),
                H("Nonnegativity of the anchor quadratic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo([Source]),
                Blocks(Paragraph(Text("For every faithful product state and Hermitian tangent with both partial traces zero, the BKM quadratic form dominates the sum of the two measured Fisher forms. Each subsystem may use any pair of rank-one mutually unbiased bases. Normalizing the two local pairs preserves faithfulness, the tangent conditions, and the quadratic itself. In the standard bases, the exact diagonal–circulant covariance estimate controls the Simpson upper bound on the dual BKM form."))), DescribeRole.Theorem))));
}
