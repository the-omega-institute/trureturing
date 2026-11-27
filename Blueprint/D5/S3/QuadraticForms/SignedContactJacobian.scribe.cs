using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SignedContactJacobianDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/QuadraticForms/SignedContactJacobian";
    private const string Digest =
        "Characterize the homogeneous signed contact equations by contact and tangent nullspaces.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, Digest, "evidence-not-specified-by-formal-manifest"),
        H("The kernel of the signed contact Jacobian"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-contact-kernel"),
                DeclarationHandle.Create(Module + ".kernel_iff"),
                H("Nullspaces of the contact and interior derivative columns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use finite row, contact and interior-index sets over a "
                        + "linearly ordered commutative ring. The contact matrix carries the "
                        + "moment vectors at all contacts. The tangent matrix carries the "
                        + "derivatives at interior contacts. Each interior curvature is "
                        + "nonzero, and each signed weight is its curvature times a strictly "
                        + "negative factor.")),
                    Paragraph(Text("For any changes in the weights, dual vector and interior "
                        + "positions, the three homogeneous equations are the linearized "
                        + "moment, contact-value and interior stationarity equations. They "
                        + "hold exactly when the change in the weights lies in the contact "
                        + "matrix kernel, the dual vector is orthogonal to all contact and "
                        + "tangent columns, and the interior position change is zero.")),
                    Paragraph(Text("Substitute the interior stationarity equation into the "
                        + "moment equation and pair with the dual vector. The contact term "
                        + "vanishes and the remaining weighted sum of squares has strictly "
                        + "positive coefficients. Each tangent pairing must vanish. The "
                        + "nonzero curvatures then force the interior motion to vanish.")),
                    Paragraph(Text("Over the reals the criterion gives a trivial kernel "
                        + "when the contact columns are independent and the contact and "
                        + "tangent columns together span the moment space. Establishing "
                        + "these rank conditions for a particular spectrum requires its "
                        + "own bounds on the contact and tangent columns."))),
                DescribeRole.Theorem))));
}
