using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Jacobi;

internal sealed class NeumannHeatGramianJetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Jacobi/NeumannHeatGramianJet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-net input removes an additive constant in the endpoint heat response. For two positive Neumann paths with a common prefix, the first changed return moment determines the first changed Gramian coefficient.",
        H("The zero-net Gramian jet of a lumped Neumann path"),
        Blocks(
            Describe.Lean(DescribeId.Create("time-average"), DeclarationHandle.Create(Prefix + "timeAverage"),
                H("Formal time average"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient of degree r in the time average is the original coefficient divided by r+1. Multiplying the result by time gives the formal integral with zero constant term."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zero-net-gramian"), DeclarationHandle.Create(Prefix + "gramian"),
                H("The centered Gramian"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integrate the square of the heat response from zero and subtract time times the square of its mean. Shifting the response by a constant leaves this series invariant. Its derivative is the square of the difference between the time average and the response."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("positive-path"), DeclarationHandle.Create(Prefix + "Path"),
                H("Positive finite paths"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The n positive edge lengths are ordered from the measured endpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-edge"), DeclarationHandle.Create(Prefix + "edge"),
                H("Edge lengths"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Edge i joins vertices i and i+1 for i below n. The edge-length sequence is extended by zero at and beyond n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-mass"), DeclarationHandle.Create(Prefix + "mass"),
                H("Lumped vertex mass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mass at a vertex is half the sum of the lengths of its incident edges."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-diagonal"), DeclarationHandle.Create(Prefix + "diagonal"),
                H("Stiffness diagonal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide the sum of incident conductances by the vertex mass. Each conductance on the finite path is the reciprocal of its edge length."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-bond"), DeclarationHandle.Create(Prefix + "bond"),
                H("Symmetric stiffness coupling"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coupling is the negative edge conductance divided by the geometric mean of the adjacent vertex masses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-moment"), DeclarationHandle.Create(Prefix + "moment"),
                H("Physical endpoint moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the finite mass-normalized stiffness repeatedly to the endpoint unit vector. Divide the resulting endpoint coordinate by the endpoint mass for the collocated physical heat port."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-heat"), DeclarationHandle.Create(Prefix + "heat"),
                H("Formal heat response"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The degree-r coefficient is the physical moment of order r times the alternating sign divided by r factorial. An arbitrary constant offset is added to the response."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("first-reveal"), DeclarationHandle.Create(Prefix + "first_reveal"),
                H("Exact first difference after a common positive prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Consider two paths p and q with n positive edges. Let k be positive and smaller than n. Assume the paths share all edges with index below k and have unequal lengths at index k. Their Gramian difference has zero coefficients below degree 2k+2, for any pair of constant heat offsets.")),
                    Paragraph(Text("At degree 2k+2 the coefficient is the product of the negative first moment of p, the order 2k, and the order-2k moment difference p minus q, divided by the factorial of 2k+2. This coefficient is nonzero.")),
                    Paragraph(Text("The paths have the same Jacobi compression onto the first k vertices. The first return outside this compression contributes the product of squared couplings. Only the last factor varies with edge k, through the reciprocal of the mass at vertex k. In the derivative of the Gramian, the first changed centered coefficient pairs with the shared linear coefficient. Formal integration raises the degree by one."))), DescribeRole.Theorem))));
}
