using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Rauzy;

internal sealed class TribonacciInteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact exponent-zero Tribonacci Rauzy closure has nonempty interior at both secondary roots.",
            H("Interior of the Tribonacci Rauzy fractal"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("tribonacci-separated-cylinder-system"),
                    DeclarationHandle.Create(
                        "D5/S3/Geometry/Rauzy/TribonacciInterior.tribonacciCylinderSystem"),
                    H("The concrete geometric input"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The two characteristic-root hypotheses supply every field of "
                        + "the separated-cylinder system for the existing Rauzy closure. "
                        + "The interior theorem consumes this same object."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-interior-nonempty"),
                    DeclarationHandle.Create(
                        "D5/S3/Geometry/Rauzy/TribonacciInterior.rauzyFractal_interior_nonempty"),
                    H("Nonempty interior at either non-Perron root"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The only hypotheses are that z belongs to the existing complex "
                            + "Tribonacci characteristic-root multiset and is distinct from "
                            + "the real Tribonacci constant beta. K is exactly the existing "
                            + "closure of all finite Boolean digit sums starting at exponent "
                            + "zero and avoiding three consecutive ones. Neither a tile "
                            + "assumption nor positive area is supplied as a premise.")),
                        Paragraph(Text(
                            "The three-step count recurrence with initial values 1, 2, 4 "
                            + "gives at least beta^Q names at every length Q. Resultant "
                            + "separation gives disjoint balls of radius "
                            + "sqrt(beta - 1) norm(z)^Q / 2 around these actual points of K. "
                            + "The identity beta norm(z)^2 = 1 bounds their total area below "
                            + "uniformly in Q. Continuity of the compact thickenings gives "
                            + "positive area for K.")),
                        Paragraph(Text(
                            "Every finite word splits into an admissible prefix and suffix "
                            + "after terminal zero padding. The resulting affine images of "
                            + "compact K form a finite closed upper cover, which extends "
                            + "from the finite digit window to its closure. The synchronized "
                            + "cluster and persistent-hole construction then supplies a "
                            + "finite family of translates covering a disk and hence interior.")),
                        Paragraph(Text(
                            "This is classical Rauzy geometry, not a novelty claim. "
                            + "Messaoudi's Propriétés arithmétiques et dynamiques du fractal "
                            + "de Rauzy, JTNB 10(1), 135–162, provides context; its "
                            + "exponent-three convention and imported tiling result are "
                            + "not premises of the formal proof. The theorem does not "
                            + "claim connectedness, tiling, or a numerical inner ball."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Geometry/Rauzy/Interior")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/Separation")),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/Tribonacci/RauzyFractal"))
            ]));
    }
}
