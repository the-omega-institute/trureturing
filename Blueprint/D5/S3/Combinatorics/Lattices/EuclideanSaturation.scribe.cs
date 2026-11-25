using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class EuclideanSaturationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/grayson1984semistability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral bases of primitive intersections",
        H("Saturation and integral basis extension"),
        Blocks(
            Describe.Lean(DescribeId.Create("adapted-bases"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanSaturation.Adapted"),
                H("Three compatible integral bases"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Given integral submodules A and B and an integral "
                    + "basis c of their intersection, adapted bases are a basis (c,a) of A, "
                    + "a basis (c,b) of B and a basis (c,a,b) of their sum. The bases "
                    + "have exactly the same vectors in their common blocks."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("saturated-common-bases"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/EuclideanSaturation.adaptedBasesOfSaturated"),
                H("Simultaneous bases for saturated submodules"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let A and B be finitely generated saturated submodules "
                        + "of an integral submodule L in a characteristic-zero vector "
                        + "space. Any basis c of their intersection extends to compatible "
                        + "bases of A and B and to a basis of their sum. No topology or "
                        + "finite dimension of the ambient vector space is required.")),
                    Paragraph(Text("Saturation makes the quotients of A and B by their "
                        + "intersection torsion-free. These finite modules over the "
                        + "integers are free, so both quotient maps admit linear sections. "
                        + "Take the product of the intersection and the two quotients, "
                        + "and map a triple to its intersection vector plus its two "
                        + "lifted quotient vectors. Decomposing a vector of the sum into "
                        + "vectors of A and B proves surjectivity.")),
                    Paragraph(Text("For injectivity, a triple mapping to zero has its "
                        + "lifted A vector in B, hence in the intersection. Its quotient "
                        + "coordinate vanishes. The B coordinate then vanishes for the "
                        + "same reason, followed by the intersection coordinate. Transport "
                        + "the product of the three integral bases through this linear "
                        + "equivalence. The corresponding two-factor equivalences give "
                        + "the bases of A and B with the same lifted vectors."))),
                DescribeRole.Definition))));
}
