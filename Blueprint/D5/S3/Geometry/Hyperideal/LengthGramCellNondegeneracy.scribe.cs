using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramCellNondegeneracyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every strictly positive six-length vector, each of the twenty original four-point coefficient cells is an affine simplex.",
        H("Nondegeneracy of the twenty original coefficient cells"),
        Blocks(
            Paragraph(Text("The result uses the literal facet and ridge support table, so it preserves the original endpoint order and does not add a Gram-determinant or geometric-realization hypothesis.")),
            Describe.Lean(
                DescribeId.Create("vertices-affine-independent"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LengthGramCellNondegeneracy.vertices_affine_independent"),
                H("All twenty cells are affinely independent"),
                StatementSource.FromAuthor(F.Disp(F.Id("verticesAffineIndependent"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first support is the entry facet n. It is strictly nonzero at the barycenter and vanishes at the three ordered endpoint entries. The second support is ridge n; it is nonzero at the first endpoint and vanishes at the last two. The generic support-triangularization lemma then reduces an affine relation to a scalar multiple of the difference of the final two endpoints. The endpoint classification proves that those two ordered endpoints are distinct for every one of the twenty rows.")),
                    Paragraph(Text("This theorem supplies only cell nondegeneracy. It does not assert that the twenty cells cover the cut body, describe all pairwise intersections, or identify their geometric images with hyperbolic tetrahedra; those are separate claims."))),
                DescribeRole.Theorem))));
}
