using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Charge;

internal sealed class NativeChargeGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Charge/NativeChargeGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal original native ground action has the cocycle-signed reflected-charge adjoint.",
        H("The Literal Native Ground and Its Signed Inverse Adjoint"),
        Blocks(
            Paragraph(Text("Import the unchanged LatticeHalfFockChargedTensorCoefficients module. Its groundRank and "
                + "groundRepresentation are the literal two nested Classical.choose expressions, and ActualGround and "
                + "groundAction are its existing interfaces. The second choose_spec supplies rank(D)=n+n and negative "
                + "central action for exactly the chosen rho. No native definition is copied, and no equality to the "
                + "displayed quotientRepresentation witness is asserted. nativeOperatorAlgebra is consumed definitionally "
                + "at that exact carrier and representation in a compiled application of the positive-form and all-End twirl results.")),
            Describe.Lean(
                DescribeId.Create("literal-native-cocycle-signed-adjoint"),
                DeclarationHandle.Create(Prefix + "native_ground_signed_adjoint"),
                H("Reflection Is Not the Inverse Without Its Original Sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Original group multiplication gives [(0,a)] inverse=[(integralCocycle(a,a),0)] [(0,-a)]. "
                        + "The existing exact signed-translation law gives the central scalar for that sign element. "
                        + "Consequently the native positive form obeys H(groundAction(a)x,y)=epsilon(a,a) "
                        + "H(x,groundAction(-a)y). The sign is not discarded: complexSign(integralCocycle(a,a)) "
                        + "equals epsilon(a,a), and the existing integral_cocycle_square proves "
                        + "epsilon(a,a)=paritySign(bilinear(a,a)/2). All integral charges and all native states are quantified.")),
                    Paragraph(Text("This is a finite ground Hermitian adjoint result, not an invariant bilinear form "
                        + "or a Frobenius-Schur statement. It does not change the original quotient core, parity convention, "
                        + "half-norm normalization or literal choices. Its mathematics is a classical cocycle-sensitive "
                        + "inverse-adjoint consequence, not a new string, fusion, anomaly or spacetime theorem."))),
                DescribeRole.Theorem))));
}
