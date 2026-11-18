using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class BKMProjectionRigidityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/BKMProjectionRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The BKM power integral sends a Hermitian projection to a positive semidefinite "
        + "matrix exactly when the projection commutes with the faithful base.",
        H("BKM projection rigidity"),
        Blocks(
            Entry("commuting-direction", "omega_of_commute", "The integral on a commuting direction",
                "The commutation equation eliminates matrix entries between distinct eigenspaces. "
                + "On entries within an eigenspace the logarithmic mean is the eigenvalue, "
                + "so the integral is multiplication by the base."),
            Entry("projection-rigidity", "omega_projection_posSemidef_iff", "Positivity detects commutation",
                "Sandwich the BKM output by the inverse square root of the base and test "
                + "its trace pairing with the complementary projection. Its trace equals "
                + "the trace of the original projection. In a spectral basis the negated "
                + "pairing sums squared entry magnitudes weighted by the logarithmic mean "
                + "divided by the geometric mean, minus one. Each term is nonnegative, "
                + "and the coefficient is positive across distinct eigenvalues. Positivity "
                + "forces all such entries to vanish. In the converse direction the output "
                + "is positive by compression. Every projection rank is in scope."),
            Describe.Lean(
                DescribeId.Create("negative-trace"), DeclarationHandle.Create(Module + "negTrace"),
                H("Negative spectral mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the real trace of the negative part from continuous "
                    + "functional calculus."))), DescribeRole.Definition),
            Entry("projection-leakage", "omega_projection_leakage", "Off-diagonal leakage",
                "The first two terms of the hyperbolic sine series give a quadratic bound "
                + "on the logarithmic-mean coefficient. The spectral upper bound converts "
                + "logarithm differences to differences of eigenvalues. The spectral lower "
                + "bound controls the norm of the complementary projection after congruence. "
                + "The two adjoint corners have equal squared Frobenius norm, giving the "
                + "factor 12 times the squared upper bound divided by the lower bound."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
