using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class HNPCorrectionLiftAdvantageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/HNPCorrectionLiftAdvantage.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common correction budget controls the actual center increments and yields compatible reference envelopes.",
        H("Uniform ring correction budgets and reference envelopes"),
        Blocks(
            Paragraph(Text("Use s(j)=xstar*b^(-j/2), tau(j)=N*b^j and n(j,k)=tau(j)*b^k. Lift denotes the hypergeometric Bernstein elevation operator and correction is the positive-floor HNP correction from the imported module. The reference profile is 1/2+eta*phi((a+b*q)/x). Its mixed jets keep the two derivative orders and the constant term explicit.")),
            Paragraph(Text("For r<rho<r+1, rho>=2 and theta>0 there is B>=16. For every b>=B and xstar>0, A,H>=0, epsilon>0, there are D>0 and N>=3*r+2, both independent of j,f,c,M,k and the coefficient index. Under the C^r, uniform M, derivative A*s(j)^(-nu), and top Holder H*s(j)^(-rho) hypotheses, the center coefficient distance from c plus D*s(j)^(-rho) times the elevated correction is at most M+epsilon. Each increment coefficient is bounded by that same scaled D times the difference between the old correction elevated to the new degree and the new correction. Both bounds use the same center and constants.")),
            Paragraph(Text("Let chi be smooth with compact support inside (0,T), T>0, 0<=chi<=1, and beta>=0. Put phi(t)=chi(t)*t^beta and eta=2/(5*T^beta). For arbitrary real a,d and the same r,rho,theta conditions, one B>=16 works; for every b>=B and xstar>0 there are D>0,N>=3*r+2. At every ring j and every 0<x<=1 with s(j)/sqrt(b)<=x, the lower and upper coefficient arrays formed from the actual reference center and the scaled correction lie between 9/20 and 19/20, in order, for all stages and legal indices. Elevating the lower array gives a value at most the next lower array; the next upper array is at most the elevated upper array.")),
            Paragraph(Text("The reference result proves shared margins and both elevation inequalities. It does not identify a limiting target function or assert target sandwiching. The smooth compact cutoff and parameter derivatives are repository deductions; the correction construction acknowledges Holtz, Nazarov and Peres.")),
            Entry("correction-uniform-bound", "correction_uniform_bound", "Correction uniform bound",
                "For n>0, r<=n, t<=n+r, rho>=0 and theta>=0, the degree-n correction elevated to n+r is at most (theta+1)*n^(-rho/2)."),
            Entry("uniform-ring-correction-budget", "uniform_ring_correction_budget", "Uniform ring correction budget",
                "The two simultaneous coefficient bounds in the introduction use one D and N for all rings and input functions; the difference of corrections pays for the actual center increment."),
            Entry("fullqxjet-eq", "fullQxJet_eq", "Fullqxjet eq",
                "The mixed jet of the full reference function equals the mixed jet of its centered part plus 1/2 exactly when both derivative orders are zero, and plus zero otherwise."),
            Entry("profile-smooth", "profile_smooth", "Profile smooth",
                "Every recursively constructed profile of a globally smooth real function is globally smooth, for arbitrary natural initial order and recursion depth."),
            Entry("profile-compact", "profile_compact", "Profile compact",
                "Every recursively constructed profile of a compactly supported real function has compact support, without a smoothness hypothesis."),
            Entry("iterated-smooth", "iterated_smooth", "Iterated smooth",
                "Every finite iterated derivative of a globally smooth real function is globally smooth."),
            Entry("affine-iterated", "affine_iterated", "Affine iterated",
                "For every smooth phi, order ell and real a,b,x,q, the ell-th q derivative of phi((a+b*q)/x) is b^ell*x^(-ell)*phi^(ell)((a+b*q)/x). Integer powers use Lean's total inverse convention, including x=0."),
            Entry("xq-formula", "xq_formula", "Xq formula",
                "For x nonzero, differentiating first in q and then in x gives eta*b^ell*x^(-(ell+m)) times profile(phi^(ell),ell,m) evaluated at (a+b*q)/x."),
            Entry("qx-formula", "qx_formula", "Qx formula",
                "For x nonzero, differentiating first in x and then in q gives eta*b^ell*x^(-(m+ell)) times the ell-th derivative of profile(phi,0,m) at (a+b*q)/x."),
            Entry("cutoff-smooth", "cutoff_smooth", "Cutoff smooth",
                "For smooth chi supported in the strictly positive half-line and any real beta, the function chi(t)*t^beta is globally smooth, including at zero."),
            Entry("cutoff-reference-mixed-scales", "cutoff_reference_mixed_scales", "Cutoff reference mixed scales",
                "For smooth compact chi supported in the positive half-line, arbitrary beta,eta,a,b and c>0, each pair m,ell admits a positive K bounding both mixed jets by K*s^(-(m+ell)) for every s,x>0 with s/c<=x and every q. In addition, each m,r and 0<alpha<=1 admits a positive K: when also x<=1, all full mixed jets through order r are bounded by K*s^(-(m+r)-alpha), and the top jet has the corresponding alpha-Holder bound on all real q,q'. The constants need not be the same between the two assertions."),
            Entry("complex-jet", "complex_jet", "Complex jet",
                "On [0,1], every iterated derivative within the interval of the complex embedding of a smooth real function equals the complex embedding of its ordinary iterated real derivative, including at the endpoints."),
            Entry("reference-ring-envelopes", "reference_ring_envelopes", "Reference ring envelopes",
                "The arrays and their common margins and elevation inequalities have the full parameter range and shared constants stated in the introduction."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
