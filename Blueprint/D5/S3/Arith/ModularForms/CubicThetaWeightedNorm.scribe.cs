using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaWeightedNormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaWeightedNorm.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite Eisenstein norm fibres carry cubic phases. Six disjoint core cosets give the weighted cubic dissection.", H("CubicThetaWeightedNorm"), Blocks(
            Paragraph(Text("Complete finite Eisenstein norm fibres carry cubic phases. Six disjoint core cosets give the weighted cubic dissection.")),
            Node("0", "weightedNormCoefficient", "The complete finite Eisenstein norm fibre summed with cubic root phase.", DescribeRole.Definition),
            Node("1", "weightedNormTheta", "The power series of full finite-fibre phase-weighted norm coefficients.", DescribeRole.Definition),
            Node("2", "phase_mod", "The cubic phase depends only on its integer exponent modulo three.", DescribeRole.Theorem),
            Node("3", "hasSum_weighted_norm", "The entire root-weighted integer lattice sum has the finite-fibre coefficients.", DescribeRole.Theorem),
            Node("4", "weighted_norm_three_mul", "The residue-zero weighted fibre identifies with the norm fibre at the divided degree.", DescribeRole.Theorem),
            Node("5", "weighted_norm_three_mul_add_one", "The six disjoint core cosets have total phase weight minus three.", DescribeRole.Theorem),
            Node("6", "weighted_norm_three_mul_add_two", "The residue-two norm fibre is empty, so its weighted coefficient vanishes.", DescribeRole.Theorem),
            Node("7", "weighted_norm_dissection", "The full root-weighted lattice theta has the exact cubic dissection.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. Classical theta mathematics is attributed to Borwein and Cooper as quoted in Huang et al. arXiv:2507.16644v1. The repository InversionSeq207 triple-product supplier is reused. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubicthetaweightednorm-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
