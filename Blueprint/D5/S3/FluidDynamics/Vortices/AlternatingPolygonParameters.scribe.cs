using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The genuine domain is the set of collision-free Cartesian configurations. The field uses Cartesian Eqs. (1)-(2), with arbitrary positive b and Omega. The positive radius is sqrt(b/(4 Omega)). Field and Jacobian scaling are derived from these equations. For every N at least three and any positive radius and orientation, equilibrium is equivalent to even N and the specified radius. The odd proof uses tangential readout and total charge one, without assuming an even reflection symmetry.",
        H("Alternating Polygon Parameters"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("collision_free_rotate", "Collision freedom under physical rotation", "A common rotation preserves the genuine collision-free domain used when differentiating the actual field.", DescribeRole.Theorem),
            Node("CollisionFree", "CollisionFree", "The genuine domain of the Cartesian point-vortex equations.", DescribeRole.Definition),
            Node("field", "field", "Cartesian Eqs. (1)--(2), interpreted on `CollisionFree` configurations.", DescribeRole.Definition),
            Node("jacobian", "jacobian", "Partial derivatives of the actual field, at the specified configuration.", DescribeRole.Definition),
            Node("radius", "radius", "The physical radius is the positive square root of b/(4*Omega).", DescribeRole.Definition),
            Node("field_differentiable_at", "field differentiable at", "On collision-free configurations every interaction denominator is nonzero, so the actual field has a Frechet derivative.", DescribeRole.Theorem),
            Node("collision_free_smul", "collision free smul", "Multiplication by a nonzero radius preserves and reflects collision freedom.", DescribeRole.Theorem),
            Node("radius_pos", "radius pos", "Positive b and Omega give a strictly positive radius.", DescribeRole.Theorem),
            Node("radius_sq", "radius sq", "The chosen radius satisfies R squared = b/(4*Omega).", DescribeRole.Theorem),
            Node("normalized_field", "normalized field", "The parameterized Cartesian field at b=2 and Omega=1/2 equals the existing canonical field.", DescribeRole.Theorem),
            Node("field_scaling", "field scaling", "For nonzero R and b=4*Omega*R squared, the actual field at R*w is 2*Omega*R times the normalized field at w, on its collision-free domain.", DescribeRole.Theorem),
            Node("polygon_collision_free", "polygon collision free", "The canonical polygon belongs to the genuine domain of the field.", DescribeRole.Theorem),
            Node("normalized_differentiable", "normalized differentiable", "Existence of the actual multivariable derivative at every normalized polygon.", DescribeRole.Theorem),
            Node("jacobian_scaling", "jacobian scaling", "Differentiating the field scaling yields the equality of actual Cartesian Jacobians at every canonical polygon.", DescribeRole.Theorem),
            Node("scaled_equilibrium", "scaled equilibrium", "Positive physical parameters select a strictly positive equilibrium radius.", DescribeRole.Theorem),
            Node("rotate", "rotate", "A simultaneous physical rotation of all vortex positions.", DescribeRole.Definition),
            Node("regular", "regular", "The trap-centered polygon, with arbitrary radius and orientation.", DescribeRole.Definition),
            Node("field_rotation", "field rotation", "Rotational covariance follows from the Cartesian equations and distances.", DescribeRole.Theorem),
            Node("regular_collision_free", "regular collision free", "Every positive-radius regular polygon is collision-free, including odd N.", DescribeRole.Theorem),
            Node("angular_readout", "angular readout", "The tangential Cartesian readout uses only equal nonzero radii and distinct points. It requires no odd-pattern radial cancellation.", DescribeRole.Theorem),
            Node("total_charge", "total charge", "The specified alternating pattern has total charge zero for even N and one for odd N.", DescribeRole.Theorem),
            Node("odd_nonstationary", "odd nonstationary", "An odd cyclic charge pattern still defines the Cartesian field. Its positive vortex has nonzero tangential velocity at every positive radius.", DescribeRole.Theorem),
            Node("regular_equilibrium_iff", "regular equilibrium iff", "Sharp actual-field boundary for the specified cyclic charge pattern.", DescribeRole.Theorem),
            Node("regular_equilibrium_iff_radius", "regular equilibrium iff radius", "Positive radii identify the square-root radius without a sign ambiguity.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-parameters-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
