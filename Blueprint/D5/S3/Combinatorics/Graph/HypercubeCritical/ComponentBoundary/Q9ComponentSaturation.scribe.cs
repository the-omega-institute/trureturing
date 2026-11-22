using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ComponentSaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Huang saturation with residual vertices",
        H("A constraint on all 258-vertex candidates"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia's Problem 2 asks whether 258 vertices of the nine-cube can induce maximum degree at most three. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("q9-two-weighted-singular-components"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/"
                    + "Q9ComponentSaturation.exists_two_weighted_singular_components"),
                H("Two actual components are singular at every coordinate weighting"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a parity and let K be the weighted signed matrix from its selected vertices to the opposite-parity exterior. There are two more rows than columns. The coordinate flips anticommute, so the square of the ambient signed operator is the sum of the squared weights times the identity. Splitting the square along the selected and exterior columns identifies the defect with the Gram matrix of K. Its blocks lie on actual connected components.")),
                    Paragraph(Text("The full defect is singular over the polynomial ring in the nine weights. Choose one singular block and delete a row and its matching column within it. At unit weights a vector in the rooted defect kernel extends to a supported Huang eigenvector. Vanishing at the root propagates through the connected subcubic component, so the rooted block is invertible there. The rooted determinant polynomial is therefore nonzero. The full defect after deleting one row and column is still singular by the row count. Factoring its determinant gives another singular block. Both zero polynomial determinants remain zero at every real specialization.")),
                    Paragraph(Text("A proposed candidate can be rejected by exact determinant evaluations if they rule out universal singularity on all but one of its connected components. The test allows additional selected vertices outside the two components. The existence of a 258-vertex candidate remains open."))),
                DescribeRole.Theorem)),
        []));
}
