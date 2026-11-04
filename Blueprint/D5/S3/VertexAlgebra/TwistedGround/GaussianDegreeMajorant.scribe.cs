using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class GaussianDegreeMajorantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/GaussianDegreeMajorant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A creation recurrence gives an all-degree Gaussian square-mass bound.",
        H("Gaussian degree majorant"),
        Blocks(
            Paragraph(Text("For nonnegative a(n), a(0)=1 and (n+1)a(n+1) <= (c+r*n)a(n), where c>=0 and 0<=r<1, the proofs derive a uniform exponential bound and summability. Neither summability nor a Gaussian norm identity is assumed. The recurrence is supplied by the polynomial creation/derivative estimate in FactorialFockQuadraticEstimate.")),
            N("partial_sum_bound", "Uniform bound for every particle cutoff", "For every N, the sum of a(n) from zero through N is at most exp(c/(1-r)). For the finite polynomial F_N(t), the recurrence gives F_N'(t) <= c/(1-r)*F_N(t) on [0,1]. The integrating factor exp(-c*t/(1-r)) has nonpositive derivative. All sums in this argument are finite."),
            N("summable_of_creation_recurrence", "Infinite particle-number summability", "The uniform finite partial-sum bound and nonnegativity imply Summable a using the existing Mathlib real series criterion."),
            N("tsum_bound", "Bound for the complete series", "The full sum is at most exp(c/(1-r)); no infinite differentiation or interchange is used."),
            Paragraph(Text("For Gaussian Fock degrees take c=HS(A)^2/2 and r=q^2. This module makes no actual-source/Wick identification, determinant identification or physical realization claim."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("gaussian-degree-majorant-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
