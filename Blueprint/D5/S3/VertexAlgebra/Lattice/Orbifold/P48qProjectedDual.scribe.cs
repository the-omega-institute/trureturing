using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qProjectedDualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.";
    private static readonly LibraryNoteRef Nebe =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");
    private static readonly LibraryNoteRef BakalovKac =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The P48q lattice equals its Gram dual, and the dual of its integral fixed lattice is the image of the order-three average on integral charges.",
        H("P48q Gram Dual and Projected Charges"),
        Blocks(
            Paragraph(Text("Use the Nebe–Sloane P48q catalogue basis with coordinates indexed by Fin 48. "
                + "Let G be the integral Gram matrix and B its complex bilinear extension. Write ι for "
                + "coordinatewise inclusion of the integer rows into the complex rows. Let A be the fourth "
                + "power of the first catalogue generator, acting on rows by right multiplication. Write "
                + "T for its complex linear extension and N = I + A + A² for the integral cyclic norm.")),
            Describe.Lean(
                DescribeId.Create("gram-dual-iff"),
                DeclarationHandle.Create(Prefix + "gram_dual_iff"),
                H("The ambient Gram dual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(
                    Paragraph(Text("For every complex row μ, the pairing B(ι(x), μ) is an integer in ℂ "
                        + "for every integer row x if and only if μ = ι(a) for some integer row a.")),
                    Paragraph(Text("Testing the coordinate unit rows gives an integral column Gμᵀ. "
                        + "Applying the certified integral inverse recovers integral coordinates for μ. "
                        + "In the reverse direction, the Gram matrix has integer entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-dual-iff-projected-charge"),
                DeclarationHandle.Create(Prefix + "fixed_dual_iff_projected_charge"),
                H("The fixed dual is the image of the average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe, BakalovKac),
                Blocks(
                    Paragraph(Text("For every complex row μ, the conjunction of Tμ = μ and integrality "
                        + "of B(ι(x), μ) for every integer row x with xA = x holds if and only if "
                        + "μ = ι(aN)/3 for some integer row a.")),
                    Paragraph(Text("The isometry gives B(ι(x), 3μ) = B(ι(xN), μ) when μ is fixed. "
                        + "Since xN is fixed, the ambient dual theorem puts 3μ in the integral lattice. "
                        + "The integral norm-image certificate supplies a with ι(aN) = 3μ. Conversely, "
                        + "the average of a is fixed and pairs with any fixed integral x exactly as a does.")),
                    Paragraph(Text("This is the P48q coordinate proof of the lattice equality "
                        + "(Q ∩ h₀)* = π₀(Q*) used after equation (4.56) of Bakalov–Kac, "
                        + "arXiv:math/0402315v1, with the projection-duality identity in Lemma 4.6. "
                        + "Here the ambient dual equals Q and π₀ is the order-three average."))),
                DescribeRole.Theorem))));
}
