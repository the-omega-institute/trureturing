using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SpectralCentralizerEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/SpectralCentralizerEquality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compressed centralization constructs one all-threshold optimal spectral family and suffices for original operational equality.",
        H("Sufficiency for the original prescribed pair"), Blocks(
            Paragraph(Text("Let M act on an arbitrary complex Hilbert space in universe v. The original positive continuous dual inputs rho and sigma belong to the independently defined coefficient-series predual. Form the genuine GNS of psi=rho+sigma and keep any actual coordinate C furnished by original_pair_coordinate: 0<=C<=I, C commutes with the represented algebra, and the coefficients of C and I-C equal the original rho and sigma. No nonzero, normalized, faithful, separable, finite-dimensional or full-support premise is imposed.")),
            Node("spectral_overlap_optimal", "One spectral family attains every overlap", "Assume CompressedCentralizes for the actual GNS commutant, C and its unnormalized cyclic vector. Here P is the range support of C(I-C), and the hypothesis compares the two vector coefficients of PCP and PYP only inside this corner. The existing compiled criterion gives maximality of G_t=min(C,t(I-C)) against every feasible operator of that commutant. For any positive dual eta below rho and t sigma, domination by rho+sigma constructs its unique actual GNS coordinate X. The actual coefficient-order reflection proves X<=C and X<=t(I-C). The ambient criterion bounds its mass by the spectral overlap. Conversely the existing attained normal-overlap theorem bounds the spectral family by the actual original normal-overlap maximum v(t). These two comparisons give equality for this same family at every t>0. The competitor needs no extra coefficient-series premise.", true),
            Node("spectral_centralizer_equality", "Literal original sufficient direction and full L1 realization", "For every real f convex on the positive ray, the literal original maximalValue in source universe u may be extended-valued. The constructed spectral family is optimal at every positive threshold. Restricting this equality to the actual curvature support gives finite compatibility by finite_compatibility_iff_simultaneous. NormalOverlapCurvatureEquality.finite_compatibility_implies_original_equality gives maximalValue=hockeyValue without a finite-value premise, and NormalOverlapOperational.originalHockeyValue_eq_overlap identifies hockeyValue with originalHockeyValue in the same original universe. No operator-convex or full-curvature-support premise is used. The very same spectral family has a continuous complex-linear realization Gamma on its entire complex L1 space: all continuous moments agree, every output is order-normal and a coefficient series, positivity and scalar mass hold for every L1 input, norm is at most one, and both original posterior moments are exact. The predual output condition is obtained from standard_posterior_realization, not from an identification of all order-normal duals with coefficientSpace.", true),
            Paragraph(Text("This is the sufficient direction of the localized-centralizer classification. General GNS positive-moment lifting and necessity from equality are separate mathematical questions. The fixed-pair spectral construction and the compressed operator criterion supply this direction. Worldwide novelty is not claimed."))
        )));

    private static DocumentBlock Node(string name, string title, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("spectralcentralizerequality-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
