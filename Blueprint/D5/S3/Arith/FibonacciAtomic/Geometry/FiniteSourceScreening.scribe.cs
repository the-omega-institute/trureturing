using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class FiniteSourceScreeningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite counting resolvent bridge is specified on the actual all-occurrence source.",
        H("Finite Source Screening"), Blocks(
            Def("unitInverse", "finitesourcescreening-unit-inverse", "For a complete real inner-product space, unitInverse attaches the inverse continuous linear map to an explicit IsUnit proof."),
            Def("ActualBridge", "finitesourcescreening-actual-bridge", "For each source index n, ActualBridge records the actual closed counting Laplacian on the all-occurrence node space, its normalized root source and root evaluation, the supported path decomposition, the counting energy identity, symmetry and positivity, the root and source pairings, full-H screening invertibility, node resolvent invertibility, and the centered Gram covariance identity."),
            Def("root_response", "finitesourcescreening-root-response", "For an ActualBridge and positive screening parameter, root_response evaluates the actual root source response using the inverse of its counting Laplacian plus lambda."),
            Def("screened_inverse", "finitesourcescreening-screened-inverse", "For an ActualBridge and positive screening parameter, screened_inverse is the inverse on the full common edge Hilbert space of I plus N(n) times lambda times the centered finite covariance."),
            Paragraph(Text("The structure keeps the source node spaces dependent on n and keeps the common edge space fixed. Its fields state the supported-edge reconstruction, the unit-conductance counting energy, the uniform-to-counting N(n) factor, and the full-H inverse conditions. The final scalar identity is intentionally left at the source bridge until those fields are constructed from the actual address edges.")))));

    private static DocumentBlock Def(string name, string id, string prose) => Describe.Lean(
        DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
