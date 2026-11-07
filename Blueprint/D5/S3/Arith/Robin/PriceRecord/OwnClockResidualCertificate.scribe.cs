using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class OwnClockResidualCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/OwnClockResidualCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite real-image residual certificate for the canonical own-clock objective, uncompiled candidate",
        H("Finite real-image residual certificate for the canonical own-clock objective, uncompiled candidate"),
        Blocks(
            Paragraph(Text("For a finite distinct natural support S with every p>=2 and theta(S)>1, this source consumes the repaired global 25/36 response Lipschitz theorem and the actual compact-sublevel unique_real_minimum theorem. It defines lambda=1/(L log L), the literal boundary coordinates b_p=max(1,log(1+lambda^-1)/log p-1), J_L(T)=Phi terminal tangent remainder, and Q(L)=Phi(b)+J_L(F(L)). The source keeps the original OwnClockFixedSupport.phi, realValues and realInfimum unchanged.")),
            Paragraph(Text("The price identity is exact for every feasible finite chart vector: Phi(x)=Q(L)+sum_p priceLoss_p(lambda,x_p)-J_L(T(x)). Each price loss is nonnegative by the actual one-coordinate boundary maximum, including the C=p^2 tie. At the attained minimizer supplied by unique_real_minimum, the clock is the constructed fixed point tau; the feasible boundary vector supplies the opposite infimum inequality. No stationarity sufficiency, global affine convexity, replacement infimum or assumed minimizer is introduced.")),
            Paragraph(Text("The scalar curvature supplier differentiates f(t)=log(log t) twice on the actual ray. Its weight a(t)=(1+log t)/(t^2(log t)^2) is positive and antitone on [H,infinity), proved by the pinned derivative and antitone-on-derivative API. Fundamental-theorem interval integrals are written in both orientations L<=T and T<=L, then bounded by the constant curvature weight to obtain 0<=J_L(T)<=a(H)(T-L)^2/2. Combining the exact residual displacement |tau-L|<=36/11*|F(L)-L| gives the coefficient 648/121 with no additional /2.")),
            Paragraph(Text("The source is implementation-only: no compiler, kernel, axiom, Scribe, report, freeze, official acceptance, RH, finite5040 or global physical conclusion is claimed. The finite theorem is a genuine real-image enclosure; prime-prefix asymptotics and integer-image transfer remain separate obligations.")),
            Describe.Lean(DescribeId.Create("actual-ownclock-residual-boundary-clock"),
                DeclarationHandle.Create(Prefix + "boundary_clock_eq_response"), H("Boundary coordinates have the canonical response clock"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L on the valid theta ray, positive log weights turn the boundary formula with lambda=1/(L log L) into the literal max response, including equality at activation ties. The proof is a finite sum identity over the same support S."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-residual-fixed-clock"),
                DeclarationHandle.Create(Prefix + "fixed_clock_residual"), H("Fixed-point residual controls clock displacement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The global 25/36 Lipschitz estimate and the actual fixed-point equation give |tau-L| <= 36/11*|F(L)-L|. The estimate is derived from the response map and does not assume a second fixed point or a new minimizer premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-residual-enclosure"),
                DeclarationHandle.Create(Prefix + "real_infimum_residual_enclosure"), H("Exact finite real-image infimum enclosure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every L>=theta, Q(L)-(648/121)*a(theta)*(F(L)-L)^2 <= realInfimum S <= Phi(b(L)), where a(theta)=(1+log theta)/(theta^2(log theta)^2). The lower bound uses the canonical price-loss identity, genuine attained-minimum and clock identification, both Taylor-integral orientations, and the exact 648/121 algebra. No baseline subtraction occurs in this finite theorem."))), DescribeRole.Theorem))));
}
