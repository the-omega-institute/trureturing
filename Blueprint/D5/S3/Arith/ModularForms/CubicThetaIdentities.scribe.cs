using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaIdentitiesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaIdentities.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two classical cubic theta identities follow from genuine Euler products, complete lattices, and expanding coefficient induction.", H("CubicThetaIdentities"), Blocks(
            Paragraph(Text("The two classical cubic theta identities follow from genuine Euler products, complete lattices, and expanding coefficient induction.")),
            Node("0", "E", "The actual Euler series supplied by Mathlib's pentagonal product theorem.", DescribeRole.Definition),
            Node("1", "P", "The unit reciprocal of the actual Euler series.", DescribeRole.Definition),
            Node("2", "expand3", "The rational power-series algebra homomorphism substituting X cubed.", DescribeRole.Definition),
            Node("3", "B", "The actual quotient E(X)^3/E(X^3).", DescribeRole.Definition),
            Node("4", "euler_mul_inverse", "The Euler series times its normalized unit reciprocal equals one.", DescribeRole.Theorem),
            Node("5", "core_eq_product", "The full core lattice series equals the actual quotient E(X^3)^3/E(X).", DescribeRole.Theorem),
            Node("6", "B_dissection", "This first cubic identity identifies an actual Euler quotient with the lattice dissection.", DescribeRole.Theorem),
            Node("7", "quotient_multiplication", "The quotient multiplication law is proved using only the two actual unit inverses.", DescribeRole.Theorem),
            Node("8", "cubic_defect_recurrence", "The cubic defect satisfies a positive-degree expanding homogeneous recurrence.", DescribeRole.Theorem),
            Node("9", "cubic_identity", "Both sides are the actual classical series; coefficient induction closes every degree.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. Classical theta mathematics is attributed to Borwein and Cooper as quoted in Huang et al. arXiv:2507.16644v1. The repository InversionSeq207 triple-product supplier is reused. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubicthetaidentities-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
