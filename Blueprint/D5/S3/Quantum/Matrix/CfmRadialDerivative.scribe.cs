using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CfmRadialDerivativeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CfmRadialDerivative";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The derivative of the three-resolvent map and trace duality reduce radial convexity to endpoint positivity.",
        H("Resolvent derivatives and radial distance"),
        Blocks(
            Definition("Mat", "The matrix space", "Complex n×n matrices carry the Loewner order and their usual finite-dimensional topology."),
            Definition("cayleyDomain", "The Cayley interval", "The Hermitian interval −I<X<I is expressed by positive definiteness of I+X and I−X."),
            Definition("resolventDerivative", "The sandwich derivative", "The derivative at X of R_s(X)=(sI−X)⁻¹ is K↦R_s(X)KR_s(X)."),
            Definition("resolventSum", "The three-resolvent map", "The map is g(X)=R_2(X)+R_3(X)−εR_4(X), with ε any real parameter."),
            Definition("resolventSumDerivative", "The derivative of g", "The actual derivative is K↦R_2KR_2+R_3KR_3−εR_4KR_4. The final negative term is retained."),
            Definition("EndpointPositive", "Positivity at both endpoints", "For every ordered pair U≤V in the Cayley interval, both Dg_U(g(V)−g(U)) and Dg_V(g(V)−g(U)) are positive semidefinite."),
            Describe.Lean(DescribeId.Create("cfm-radial-derivative-endpoint-positive"),
                DeclarationHandle.Create(Module + ".radial_of_endpoint_positive"),
                H("Positive endpoint derivatives imply radial convexity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every ordered U≤V in the Cayley interval, suppose both "
                    + "Dg_U(g(V)−g(U)) and Dg_V(g(V)−g(U)) are positive semidefinite. "
                    + "Then every ordered triple A≤C≤B in that interval satisfies both Frobenius radial distance inequalities.")),
                    Paragraph(Text("Matrix inversion is differentiated at invertible shifts by the normed-algebra inverse derivative. "
                    + "All shifts sI−X for s=2,3,4 are positive definite. Cyclicity of trace gives "
                    + "tr(H Dg_X(K))=tr(Dg_X(H) K), and the trace product of positive semidefinite matrices is nonnegative. "
                    + "Vectorization identifies this trace pairing with the real Hilbert inner product. "
                    + "The general endpoint derivative criterion then applies. No commutation between distinct endpoints is required."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string explanation) =>
        Describe.Lean(DescribeId.Create("cfm-radial-derivative-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);
}
