using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class OriginalRingEnvelopeScaleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/OriginalRingEnvelopeScale.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One initial degree controls every original ring center; elevated corrections have a uniform advantage.",
        H("Original ring centers and elevated corrections"),
        Blocks(
            Paragraph(Text("Use the common-grid center C(tau,b,r,f,k), normalized Bernstein coefficients c(D,J,P), and endpoint scale delta of the imported Lorentz modules. The ring scale is s(j)=xstar*b^(-j/2). All centers retain the original Q initialization and residual recurrence. Complex-valued and signed inputs are allowed.")),
            Paragraph(Text("For r<rho<r+1 a threshold B at least 2 is chosen first. For each b at least B there is one positive K, independent of tau,f,c,M,A,H,s,k,J. Assume tau>0, r<=tau, f is C^r on [0,1], M,A,H are nonnegative, s>0, |f-c|<=M, derivatives of orders nu=1,...,r have modulus at most A*s^(-nu), and the top Holder seminorm is at most H. Every degree tau*b^k+r coefficient of C(tau,b,r,f,k), after subtracting c, has modulus at most M+K*A*sum(nu=1,...,r; tau^(-nu/2)*s^(-nu))+K*H*tau^(-rho/2). The initial derivative estimate uses nu/2, without claiming the sharper ceiling(nu/2) exponent.")),
            Paragraph(Text("Consequently, for any xstar>0, A,H>=0 and epsilon>0, one N at least 3*r+1 works for all rings j, inputs f, centers c, nonnegative M and stages k when the derivative and Holder bounds use s(j). Every center coefficient is within M+epsilon of c. This is a center margin, not a full envelope or cost theorem.")),
            Paragraph(Text("The same source module contains the consumed hypergeometric elevation interface. Its weight is choose(K,k)*choose(N-K,n-k)/choose(N,n), its lift sums these weights against an array, its sample is k*(K-k)/K^3, and its correction is theta/K^rho+sample^(rho/2), with natural subtraction in K-k. The finite-moment helpers retain the TauCeti source attribution and Apache license already specified in the Lean source. These auxiliaries organize existing identities; the common-center estimate supplies the substantive dependency.")),
            Entry("residual-coefficient-control", "residual_coefficient_control", "Residual coefficient control",
                "For rho>r there is K>0 uniform in n,b,f,P,A and J. If n>0, r<=n*b, b>=1, A>=0 and every residual derivative through r is bounded by A*delta(n,x)^(rho-nu), then the degree n*b+r coefficient of Q(n*b,r,f-P) is bounded by K*A*(b*(r+1))^rho*delta(n*b,J/(n*b+r))^rho."),
            Entry("delta-upper", "delta_upper", "Delta upper",
                "For n>0 and x in [0,1], delta(n,x)<=n^(-1/2), including the reciprocal-degree endpoint floor."),
            Entry("center-coefficient-control", "center_coefficient_control", "Center coefficient control",
                "The common coefficient estimate in the introduction holds for every stage and legal coefficient, using one K for each allowed refinement b."),
            Entry("ring-scale-cancel", "ring_scale_cancel", "Ring scale cancel",
                "For N,b positive, xstar>0, every natural j and real e, (N*b^j)^(-e/2)*s(j)^(-e)=N^(-e/2)*xstar^(-e). This normalization is consumed by the uniform ring budgets."),
            Entry("uniform-ring-center-margin", "uniform_ring_center_margin", "Uniform ring center margin",
                "A single initial N controls all ring indices, all admissible inputs and all stages with the stated M+epsilon margin."),
            Entry("weight-sum", "weight_sum", "Weight sum",
                "When K<=N and n<=N, the sum of the hypergeometric weights for k=0,...,n equals one, including degenerate legal parameters."),
            Entry("correction-lift-lower", "correction_lift_lower", "Correction lift lower",
                "For K<=N, n<=N, K>=2 and rho>=2, the elevated correction is at least theta/K^rho+[p*(1-p)/(2*K)]^(rho/2), where p=n/N. Theta is any real number."),
            Entry("correction-lift-upper", "correction_lift_upper", "Correction lift upper",
                "For 0<K<=N<=2*K, n<=N and rho>=0, the elevated correction is at most theta/K^rho+[4*p*(1-p)/K]^(rho/2), where p=n/N. Theta is any real number."),
            Entry("correction-lift-pos", "correction_lift_pos", "Correction lift pos",
                "For 0<K<=N, t<=N and theta>0, the elevated correction at t is strictly positive for every real rho."),
            Entry("correction-lift-advantage", "correction_lift_advantage", "Correction lift advantage",
                "If n>=2, m>=16*n, r<=m, t<=m+r, rho>=2 and theta>=0, twice the correction on degree m elevated to m+r is at most the degree-n correction elevated first to n+r and then to m+r. If theta>0, the new correction is strictly less than this twice-elevated old correction."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
