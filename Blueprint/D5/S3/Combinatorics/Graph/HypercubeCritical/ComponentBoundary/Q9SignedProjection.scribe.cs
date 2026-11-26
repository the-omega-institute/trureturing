using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed projection bound for opposite dimers",
        H("Signed projection bound for opposite dimers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-signed-projection-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedProjection.signed_projection_bounds"),
                H("Negative compatible incidences bound the omitted-row projection energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let R be the signed omitted-row matrix, m the signed source on missing rows, and k the column counts of selected compatible faces. Assume the Gram matrix RᵀR is positive definite with nonpositive off-diagonal entries, Rᵀm = −k, and RᵀRq = k. The positive and negative parts of q have disjoint support. Testing the Gram equation against the negative part proves that q is entrywise nonnegative.")),
                    Paragraph(Text("Assume each source value has magnitude at most one and the signed products mᵢRᵢⱼ are 0 or ±1. A row without a negative incidence contributes at least mᵢ² to the squared residual. Every other row can reduce that term by at most one. The residual is orthogonal to Rq, so the total reduction equals the projection energy qᵀk = ‖Rq‖². This bounds the energy by the actual number of negative incidences.")),
                    Paragraph(Text("In each column, the source identity makes twice the negative count equal the number of nonzero missing incidences plus the selected face count. If rank-four columns have at most four compatible faces and other columns have none, the energy is at most twice the number of rank-four columns.")),
                    Paragraph(Text("For the order-102 opposite-dimer branch of Hong, Wu and Xia's Problem 2, the geometric inputs are the switched Huang column Gram identity RᵀR = 4I − A for the contact graph A, the signed source identity from the compatible triples, and the rank-four face cap. Invertibility of the Gram matrix gives positive definiteness and the resolvent solution. With these inputs, seven dimers give a resolvent value at most 14, below the required 16. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
