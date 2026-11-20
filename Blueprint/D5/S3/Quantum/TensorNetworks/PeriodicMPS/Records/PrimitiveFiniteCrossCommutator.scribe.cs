using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveFiniteCrossCommutatorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveFiniteCrossCommutator";
    private const string Title = "Finite-ring cross commutation for the primitive periodic collision";
    private static LibraryNoteRef CollisionSource => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title + ".", H(Title),
        Blocks(
            Claim("collisionCommutatorMatrix", "The fixed visible commutator matrix",
                "In visible order 00, 01, 10, 11, the four rows of K are (1,0,0,1), "
                + "(0,−1,−1,0), (0,−1,−1,0) and (1,0,0,1).",
                DescribeRole.Definition),
            Claim("collision_flattening_cross_commutator", "Exact commutator of the finite cross reduction",
                "For every m ≥ 0, put n = m + 2 and let Wᵦ be the normalized amplitude flattening "
                + "for label b, with the first two sites indexing its rows. The literal 4 by 4 "
                + "cross reduction is Sₙ = W₀W₁†. With R = collisionMarginal, "
                + "RSₙ − SₙR = 12((−8)ᵐ + (8i)ᵐ)/(√200)ⁿ times K. "
                + "The matrix R is the common two-site density for m ≥ 5."),
            Claim("collision_flattening_cross_commute_iff", "Commutation exactly at ring lengths divisible by four",
                "For every m ≥ 0, R commutes with W₀W₁† exactly when (m + 2) mod 4 = 0. "
                + "The fixed matrix K has a unit entry and the scalar vanishes exactly when "
                + "m mod 4 = 2."))));

    private static DocumentBlock Claim(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("primitive-finite-cross-commutator-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(CollisionSource), Blocks(Paragraph(Text(prose))), role);
}
