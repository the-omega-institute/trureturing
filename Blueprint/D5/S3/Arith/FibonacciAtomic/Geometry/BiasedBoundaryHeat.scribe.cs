using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryHeatDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryHeat.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original real centered boundary space G0 carries a spectral heat semigroup whose generator is exactly minus the original boundary operator on its entire centered domain.",
        H("Real Heat of the Actual Centered Boundary Operator"), Blocks(
            Describe.Lean(DescribeId.Create("biasedboundaryheat-definition"),
                DeclarationHandle.Create(Prefix + "heat"), H("The Real Heat Multiplier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a real Hilbert basis e of the original G0 and positive covariance eigenvalues mu, heat(e,mu,t) transports the bounded coordinate multipliers exp(-t/mu(i)) through e.repr. Time t is nonnegative. The map acts on every vector of G0; it does not replace that space by finite sequences."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("biasedboundaryheat-generator"),
                DeclarationHandle.Create(Prefix + "actual_centered_heat"), H("The Actual Centered Heat and Generator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("One application of the actual spectral counting theorem supplies paired bases e on G0 and k on the effective edge space K, together with one positive nonincreasing covariance sequence mu tending to zero. The original Sigma and ambient C have their actual paired diagonal actions on this same family. Every repeated eigenvalue keeps its own basis occurrence.")),
                    Paragraph(Text("The transported heat operators form a strongly continuous contraction semigroup. They are positive, and their intrinsic extended positive trace is the sum of ofReal(exp(-t/mu(i))) for every nonnegative t. This statement permits infinity; finiteness for positive time requires a separate summability estimate.")),
                    Paragraph(Text("For all centered vectors u and v, the strong limit at time zero from the right of t inverse times (S(t)u-u) equals v if and only if (u,-v) lies in the original boundaryOperator graph after the original isometric inclusion into G. The parameterized polar graph and coefficient identities apply to the same e,k,mu and give the exact all-vector coefficient graph. Continuous coefficient functionals prove one direction. Finite basis projections of both the vector and its original graph image, followed by the real semigroup generator-limit theorem, prove the reverse direction.")),
                    Paragraph(Text("Any other strongly continuous contraction semigroup with this same full generator graph equals S. The multiplier, finite-span continuity and uniqueness design reuse the standard construction in DiagonalHeat and the attributed MarkovProcess supplies in ContractionSemigroup. No self-adjoint realization, inverse-domain, spectral exhaustion or counting proof is repeated.")),
                    Paragraph(Text("This centered construction does not yet assert the full-G constant-mode extension, positive-time trace-class equivalence, the quantitative heat bounds or Laplace identity, the four logarithmic limits, or the singular-value Schatten conditions for Sigma and the original C with codomain G0. Those require their own exact operator correspondences. The original constants are b=phi to the power minus two and B=2 phi cubed; the Hilbert-Schmidt assertion concerns Sigma."))), DescribeRole.Theorem))));
}
