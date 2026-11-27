// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction;

internal sealed class StandardCubicLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/StandardCubicLift.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A projected cubic isometry and projected charge inversion give a standard order-three element of the actual acting group.",
        H("Standard Cubic Lifts from Projected Inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("standard-cubic-of-projected-inversion"),
                DeclarationHandle.Create(Prefix + "standard_cubic_of_projected_inversion"),
                H("An explicit standard cubic in the acting group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("Let G act faithfully by complex linear equivalences U on the actual lattice carrier for D. "
                        + "Assume each U(t) preserves every integer vertex mode and sends the ground vector at charge a "
                        + "to the ground vector at charge(t)(a), scaled by a complex unit phase(t,a). Here charge is a group "
                        + "homomorphism to the additive automorphisms of the charge lattice under composition. Let x project "
                        + "to a bilinear isometry g of exact order three and let s project to negation.")),
                    Paragraph(Text("For y=s x s^(-1) and z=(x y)^2, the theorem gives charge(z)=g, order(z)=3, and "
                        + "phase(z,a)=1 for every charge a fixed by g. Negation commutes with g, so y projects to g "
                        + "and z projects to g^4=g. The leading charged product makes the phase of x multiplicative on "
                        + "the fixed charges. In particular its phases at a and -a multiply to one. Evaluating y s=s x "
                        + "on the ground vector at -a identifies the phase of y at a with that of x at -a. Thus x y "
                        + "and z act as the identity on each fixed-charge ground vector.")),
                    Paragraph(Text("Diagonal character conjugacy compares U(z) with the native standard lift using "
                        + "their agreement on all fixed-charge phases. The native cube is the identity on the whole "
                        + "carrier, so faithfulness gives z^3=1 in G. The nontrivial projection gives exact order three. "
                        + "A twisted conformal spectrum requires a spectral comparison for this cubic. An ambient "
                        + "associator obstruction also requires identifying the restriction to the subgroup generated "
                        + "by z with the cyclic class from the VOA."))),
                DescribeRole.Theorem))));
}
