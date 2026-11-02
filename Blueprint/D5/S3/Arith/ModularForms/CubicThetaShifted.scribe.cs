using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaShiftedEncodedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaShifted.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three affine cosets in a shifted Eisenstein lattice", H("Three affine cosets in a shifted Eisenstein lattice"), Blocks(
            Paragraph(Text("The full lattice exponent Q(x,y)-x-y is nonnegative and has finite integer fibres. Three explicit affine cosets, selected by (x-y) modulo three, identify these fibres with three copies of the previously defined core fibres.")),
            Node("0", "shiftedExponent", "The complete shifted norm Q(x,y)-x-y.", DescribeRole.Definition),
            Node("1", "ShiftedFiber", "Every integer pair at the given natural exponent.", DescribeRole.Definition),
            Node("2", "shifted_norm", "Q(3x-1,3y-1)=9(Q(x,y)-x-y)+3.", DescribeRole.Theorem),
            Node("3", "shifted_exponent_nonneg", "The shifted exponent is nonnegative at every integer pair.", DescribeRole.Theorem),
            Node("4", "shiftedFiber_finite", "Every shifted exponent fibre is finite.", DescribeRole.Definition),
            Node("5", "shiftedCoreEquiv", "The three affine cosets are disjoint and exhaust every shifted norm fibre.", DescribeRole.Definition),
            Node("6", "shiftedTheta", "The rational series counting the full shifted fibres.", DescribeRole.Definition),
            Node("lattice-sum", "hasSum_shifted_theta", "The shifted fibre series is the full monomial sum over all integer pairs.", DescribeRole.Theorem),
            Node("7", "shifted_theta_eq_three_core", "This exact all-index identity supplies the multiplicity three in the Jacobi cube.", DescribeRole.Theorem),
            Paragraph(Text("This is classical intermediate mathematics. CubicThetaCoreProduct supplies the downstream product-to-core lattice identity and EtaSignK6 supplies the exact all-index sign theorem. Independent formal acceptance and publication remain separate; no literature priority or novelty credit is asserted."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-shifted-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
