using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualSignedGaussianEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual signed endpoint without Johnston-Yang",
        H("The actual signed endpoint without Johnston-Yang"),
        Blocks(
            Paragraph(Text("The actual occurrence family is actualZero indexed by the unconditional actualOccurrenceEquiv, with every analytic multiplicity and both ordinate signs. ActualZeroLaplace supplies coefficient convergence, conjugation and mass; ActualReciprocalSquareBounds supplies strip and height; WholeFormula supplies the full actual formula; TrivialZeroLaplace supplies the complete bounded correction.")),
            Paragraph(Text("The complete Chebyshev tail identity gives Q(exp(v))=-U(exp(v))/exp(v). Factoring exp(-v) out of the absolutely convergent complete series then identifies Q(exp(v)) with signedQ, with its exact minus sign and trivial correction. There is no JY premise, truncated spectrum, absolute-value replacement or assumed signed average.")),
            Paragraph(Text("The mass conversion to ZeroCoefficientBudget.massConstant is consumed by both actual signed-spectrum instantiation and OriginalLocalA positive-peak instantiation. It reuses existing mass mathematics. These are analytic families and source identifications, not finite numerical certificates or a novelty claim.")),
            Describe.Lean(
                DescribeId.Create("actualsignedgaussianendpoint-actual-coefficient-mass"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint.actual_coefficient_mass"),
                H("The actual signed endpoint without Johnston-Yang"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing actual HasSum is normalized to 2+EulerGamma-log(4*pi) using log((2*sqrt(pi))^2). This consumed bridge introduces no assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualsignedgaussianendpoint-actual-complete-signed-gaussian-endpoint"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint.actual_complete_signed_gaussian_endpoint"),
                H("The actual signed endpoint without Johnston-Yang"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H>=20000, A>=10000 and A<=exp(H), prove actual W*Q tail integrability on the Gaussian window, its mean bound 1000*exp(-H)/H, and a point y in [H,4*(H+20)^2] with the strict signed quotient lower bound."))),
                DescribeRole.Theorem))));
}
