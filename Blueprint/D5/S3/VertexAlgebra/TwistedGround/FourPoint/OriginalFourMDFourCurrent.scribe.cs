using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDFourCurrentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDFourCurrent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original three-channel identity for four lowest-mode currents",
        H("The true D lip and its overlap with A"),
        Blocks(
            T("original-fourm-chart-d-four-current-fixed-charge", "chartD_four_current_fixed_charge",
                "The true D-lip coefficient at fixed charge",
                "Choose a lowest-mode current colour at each of P, Q, R, S, allowing repetitions. "
                + "For an integral charge of nonnegative energy and real 0 < x < 1, take degree "
                + "one in each mark and degree zero in the displacements of the physical D coefficient "
                + "on the true lip. After division by the twelfth power of the D period, this equals "
                + "−i(1−x)³/x³ times the native D-lip charge term at 1/x with occupation projection "
                + "arguments (2, 2, 0, −1) in the order P, R, Q, S."),
            T("original-fourm-chart-d-four-current-sector", "chartD_four_current_sector",
                "The coefficient in a D-lip charge sector",
                "With unit Gram determinant and positive definite real Gram form, sum the fixed-charge "
                + "formula over the charges in each mod-two sector. For real 0 < x < 1, the physical "
                + "four-current jet equals the projection of the literal true D-lip sector at 1/x, "
                + "with the same scalar, projection arguments and puncture order."),
            T("original-fourm-four-current-d-lip-crossing", "four_current_d_lip_crossing",
                "Real A/D crossing",
                "Let the lattice have rank 24, positive definite real Gram form and unit Gram determinant. "
                + "For arbitrary current colours, integers m, n, r with m + n + r = 2, any output "
                + "charge class, and real 1/2 < x < 1, the A slit channel at 1−1/x equals the true "
                + "D-lip channel at 1/x at weights (2, 2, 2). The physical A/D Fourier comparison "
                + "relates the Laurent coefficients with a common nonzero scalar. Translating the "
                + "quadratic Gauss sum cancels the Fourier normalization."),
            T("original-fourm-four-current-slit-ad-overlap", "four_current_slit_ad_overlap",
                "The complex overlap of the A and D slit channels",
                "Under the same lattice and signed-mode hypotheses, the canonical slit channels "
                + "A and D, in their respective chart parameters, agree on a complex neighborhood "
                + "of an interior point of their common chart domain for each output charge class. "
                + "The analytic D-lip continuation agrees with the canonical D channel on the open lip, "
                + "carrying the real equality to the overlap."),
            T("original-fourm-four-current-identity-k", "four_current_identityK",
                "The original signed-mode identity for the four currents",
                "For any valid even integral lattice of rank 24 with positive definite real Gram form and "
                + "unit Gram determinant, any four lowest-mode current colours, and all signed integers "
                + "m, n, r with m + n + r = 2, the original charge-coset identity K holds at weights "
                + "(2, 2, 2). The A/B and A/D overlap equalities give a common germ for the residue "
                + "identity. The certified Gram data for the actual Leech lattice supply the lattice "
                + "hypotheses, with the colour assignment and signed modes still arbitrary."))));

    private static DocumentBlock T(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
