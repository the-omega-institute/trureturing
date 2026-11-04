using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class KappaGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/KappaGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive logarithmic transforms give two-sided divergence of the complete forward response.",
        H("Two-sided unboundedness of the complete forward response"),
        Blocks(
            Paragraph(Text("The response T is the complete real-center forward response with window H=x^(4/5). Theta is the supremum of Re(rho) over zeros in the open critical strip. The lower conclusion assumes the explicitly stated Theta error estimate. The upper conclusion additionally assumes Riemann-von Mangoldt for the canonical zeta zero configuration, including its multiplicities. The positive logarithmic budget measure is the pushforward under y=log(x) of the nonnegative density (e*T(x)+k)/x on x>x0. Positive-definite Laplace boundary limits and the exact zeta residues supply the oscillation constraints.")),
            Describe.Lean(
                DescribeId.Create("budget-measure-nonnegative"),
                DeclarationHandle.Create(Prefix + "budgetMeasure_nonnegative"),
                H("Nonnegative logarithmic support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x0>=1, the pushforward by the real logarithm of the measure with density (e*T(x)+k)/x on x>x0 is supported on nonnegative real numbers. The density is read through its nonnegative part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget-exponential-integrable"),
                DeclarationHandle.Create(Prefix + "budget_exponential_integrable"),
                H("An initial convergence half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let alpha>=0 and assume |psi(t)-t|<=C*t^alpha eventually. Suppose x0>=3 and e*T(x)+k>=0 for x>=x0. The positive logarithmic budget measure has a finite exponential integral at every Laplace parameter sigma>max(0,alpha-3/10)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget-transform"),
                DeclarationHandle.Create(Prefix + "budget_transform"),
                H("The exact positive budget transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same hypotheses, the complex moment-generating function of the budget measure at -s equals e*F(s)+k*x0^(-s)/s for Re(s)>max(0,alpha-3/10). Here F is the Mellin integral of the complete forward response. The logarithmic pushforward and the density x^(-1) retain the exact Mellin Jacobian."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unbounded-below"),
                DeclarationHandle.Create(Prefix + "forward_response_unbounded_below_of_right_zero"),
                H("A right-hand zero forces negative divergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Theta be the supremum of the real parts of the nontrivial zeta zeros. Assume that for every epsilon>0 there is C with |psi(t)-t|<=C*t^(Theta+epsilon) for t>=2. If some nontrivial zero has real part greater than one half, then for all real L and X there exists x>=X with T(x)<L. A zero can be selected with beta>max(1/2,Theta-1/5); a sufficiently small positive epsilon places its shifted pole strictly inside the positive-transform convergence region."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unconditional-unbounded-below"),
                DeclarationHandle.Create(Prefix + "forward_response_unbounded_below"),
                H("Arbitrarily large negative excursions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume that for every epsilon>0 there is C such that |psi(t)-t|<=C*t^(Theta+epsilon) for t>=2. For every real L and X there is x>=X with T(x)<L. Under RH, the exponent 3/5 gives a holomorphic remainder across the imaginary axis. An eventual lower bound T(x)>=L defines a nonnegative logarithmic measure whose boundary value at zero is -L. The same-sign budget gives card(Z)<=16*L^2 for every finite set Z of nontrivial zeros. Infinitely many nontrivial zeros contradict this fixed bound. If RH fails, a zero strictly right of the critical line forces negative divergence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-kappa-gap"),
                DeclarationHandle.Create(Prefix + "forward_response_lower_kappa_gap"),
                H("The unconditional one-half lower obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the displayed Theta error estimate, for every kappa<1/2 and every real X there exists x>=X with T(x)<-kappa. This follows by taking L=-kappa in the negative-divergence theorem, which also removes the restriction kappa<1/2 from the resulting conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-kappa-gap"),
                DeclarationHandle.Create(Prefix + "forward_response_upper_kappa_gap_of_rh"),
                H("The one-half upper obstruction under RH"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under RH and the Theta error estimate, for every K<1/2 and every real X there exists x>=X with T(x)>K. Apply the nonnegative transform to K-T(x); its critical-line residue has the opposite sign and the same absolute value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unbounded-above"),
                DeclarationHandle.Create(Prefix + "forward_response_unbounded_above_of_not_rh"),
                H("Failure of RH forces positive divergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the Theta error estimate, failure of RH implies that for all real L and X there exists x>=X with T(x)>L. The functional equation supplies a zero to the right of the critical line. The transform of L-T has a nonzero shifted pole strictly inside its convergence region, which contradicts holomorphy there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rvm-unbounded-above"),
                DeclarationHandle.Create(Prefix + "forward_response_unbounded_above"),
                H("Arbitrarily large positive excursions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the Theta error estimate and Riemann-von Mangoldt for the canonical zeta zero configuration. For every real L and X there exists x>=X with T(x)>L. Under RH, an eventual bound T(x)<=L makes L-T a positive logarithmic density. Continuity and the nonzero zeta value at one half give a gap around ordinate zero. The quadratic boundary budget bounds the sum of canonical zero multiplicities in every interval shorter than this gap by 4*L^2. Dividing (T,2T] into intervals of half the gap length bounds N(T,2T) by a constant times T+1, contradicting the logarithmic factor in the Riemann-von Mangoldt lower bound. If RH fails, the existing right-hand-zero obstruction gives the conclusion without zero counting."))),
                DescribeRole.Theorem))));
}
