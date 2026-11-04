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
            Node("CollisionFree", "CollisionFree", "The genuine domain of the Cartesian point-vortex equations.", DescribeRole.Definition),
            Node("field", "field", "Cartesian Eqs. (1)--(2), interpreted on `CollisionFree` configurations.", DescribeRole.Definition),
            Node("jacobian", "jacobian", "Partial derivatives of the actual field, at the specified configuration.", DescribeRole.Definition),
            Node("radius", "radius", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Definition),
            Node("field_differentiable_at", "field differentiable at", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("collision_free_smul", "collision free smul", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("radius_pos", "radius pos", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("radius_sq", "radius sq", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("normalized_field", "normalized field", "The normalized and parameterized definitions agree at `b = 2`, `\u03a9 = 1/2`.", DescribeRole.Theorem),
            Node("field_scaling", "field scaling", "Physical scaling is asserted on the collision-free domain. The algebraic identity used to differentiate it does not assert a derivative at a collision.", DescribeRole.Theorem),
            Node("polygon_collision_free", "polygon collision free", "The canonical polygon belongs to the genuine domain of the field.", DescribeRole.Theorem),
            Node("normalized_differentiable", "normalized differentiable", "Existence of the actual multivariable derivative at every normalized polygon.", DescribeRole.Theorem),
            Node("jacobian_scaling", "jacobian scaling", "The positive-parameter Jacobian scaling is differentiated from the field identity at a collision-free polygon. It is not a presumed spectral scaling.", DescribeRole.Theorem),
            Node("scaled_equilibrium", "scaled equilibrium", "Positive physical parameters select a strictly positive equilibrium radius.", DescribeRole.Theorem),
            Node("rotate", "rotate", "A simultaneous physical rotation of all vortex positions.", DescribeRole.Definition),
            Node("regular", "regular", "The trap-centered polygon, with arbitrary radius and orientation.", DescribeRole.Definition),
            Node("field_rotation", "field rotation", "Rotational covariance follows from the Cartesian equations and distances.", DescribeRole.Theorem),
            Node("regular_collision_free", "regular collision free", "Every positive-radius regular polygon is collision-free, including odd N.", DescribeRole.Theorem),
            Node("angular_readout", "angular readout", "Tangential readout of the actual field at any equal-radius configuration. It uses no cancellation between reflected charges.", DescribeRole.Theorem),
            Node("total_charge", "total charge", "The exact declaration below uses the hypotheses and objects of this module.", DescribeRole.Theorem),
            Node("odd_nonstationary", "odd nonstationary", "An odd cyclic charge pattern still defines the Cartesian field. Its positive vortex has nonzero tangential velocity at every positive radius.", DescribeRole.Theorem),
            Node("regular_equilibrium_iff", "regular equilibrium iff", "Sharp actual-field boundary for the specified cyclic charge pattern.", DescribeRole.Theorem),
            Node("regular_equilibrium_iff_radius", "regular equilibrium iff radius", "Positive radii identify the square-root radius without a sign ambiguity.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-parameters-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
