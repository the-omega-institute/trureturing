using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class BernoulliCommonEndpointChargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite differences charge one common endpoint moment.",
        H("Finite differences charge one common endpoint moment"),
        Blocks(
            Paragraph(Text("Let Seed be any measurable space, nu a seed probability, P(p) its independent iid Bernoulli stream law, p0 in (0,1), and M a WithTop-natural stopping time for the seeded filtration. Put T_n=min(M,n), C_a(M)=M^a with value infinity at top, A(m)=((2^(2m+1)*(2m)^2)^m)*2^(2m), H(a,m)=2^a/(2^a-1)+(1-2^(a-m))^(-1), and D(m,sigma)=(2m)! sigma^(2m)(2A(m)+1). Write p(h)=proj_[0,1](p0+gamma h) and Delta_r(t,G)=sum_{i=0}^r (-1)^(r-i) choose(r,i) G(t+i t). For a horizon n and rho>0, its closed window is I_n=[rho/sqrt(n),(2m+1)rho/sqrt(n)].")),
            Describe.Lean(
                DescribeId.Create("bernoullicommonendpointcharge-bernoulli-one-scale-common-endpoint-charge"),
                DeclarationHandle.Create(Prefix + "bernoulli_one_scale_common_endpoint_charge"),
                H("A resolved window pays a positive charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every n>0, natural m>0, real a,rho,gamma,sigma,delta,S with rho>0, sigma>=0 and S>0, and real output f strongly measurable at T_n with |f|<=1 everywhere, assume the following for every h in I_n: 0<p0+gamma h<1; |gamma/(p(h)(1-p(h)))|<=sigma; |(p(h)-p0)/(p0(1-p0))| sqrt(n)<=(2A(m)+1)^(-1); and |G(h)-E_{P(p(h))}[f]|<=delta+P(p(h)){n<M}. Assume also |Delta_{2m}(rho/sqrt(n),G)|>=S n^(-a), delta n^a<=S/2^(2m+1), and the explicit calculus condition: for every U>=0, a uniform bound |D^{2m} E_{P(p(x))}[f]|<=U on I_n implies |Delta_{2m}(rho/sqrt(n),x -> E_{P(p(x))}[f])|<=(rho/sqrt(n))^(2m) U. Then S/[2(2D(m,sigma)rho^(2m)+2^(2m+1))] <= n^(a-m) E_{P(p0)}[T_n^m]. No sign assumption on a or delta is added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoullicommonendpointcharge-bernoulli-finite-dyadic-common-endpoint-charge"),
                DeclarationHandle.Create(Prefix + "bernoulli_finite_dyadic_common_endpoint_charge"),
                H("A finite family uses one endpoint law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every natural m, real a,rho,gamma,sigma,delta,S with 0<a<m, rho>0, sigma>=0 and S>0, natural J, and family of real outputs f(j) strongly measurable at T_{2^j} and bounded in magnitude by one for every j, suppose every window I_{2^j}, j<J, satisfies the rate, score, local likelihood, accuracy, signal, calculus and resolution assumptions of the preceding statement with the same G and constants. Then ofReal(J S/[2(2D(m,sigma)rho^(2m)+2^(2m+1))]) <= ofReal(H(a,m)) E_{P(p0)}^+[C_a(M)]. J may be zero. The same M and endpoint P(p0) pay every scale, although the truncated outputs may differ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoullicommonendpointcharge-bernoulli-logarithmic-common-endpoint-charge"),
                DeclarationHandle.Create(Prefix + "bernoulli_logarithmic_common_endpoint_charge"),
                H("One stopped output yields a logarithmic charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every natural m, real a,rho,C,delta,S with 0<a<m, C>=1, rho>0 and S>0, assume (2m+1)rho<=1/4 and (2m+1)rho<=(1-p0)/(2A(m)+1). Assume 0<delta<min(1/2,S/2^(2m+1))^2. Set gamma=-p0/C. Let s be an event measurable at M and G a real function satisfying |G(h)-P(p(h))(s)|<=delta for every 0<h<=1/4. For every natural j, require |Delta_{2m}(rho/sqrt(2^j),G)|>=S(2^j)^(-a). Also require the explicit uniform derivative-to-difference implication on I_{2^j} for the integrated indicator of s intersect {M<=2^j}, for every U>=0. Then ofReal(k log(delta^(-1))) <= E_{P(p0)}^+[C_a(M)], where k=S/[4(2D(m,4/(1-p0))rho^(2m)+2^(2m+1)) H(a,m) a log(2)]. The hypotheses concern one stopped output event under every positive-window parameter law. The conclusion is a conditional endpoint lower bound; it does not itself supply the finite-difference signal, the calculus implication, or a reduction from a two-source strategy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoullicommonendpointcharge-bernoulli-power-target-logarithmic-endpoint"),
                DeclarationHandle.Create(Prefix + "bernoulli_power_target_logarithmic_endpoint"),
                H("A noninteger power target supplies the logarithmic endpoint charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For a positive noninteger beta, the finite-difference signal of the power target, the stopped derivative budget and the stated window and accuracy hypotheses imply the explicit k log(delta inverse) lower bound for the common endpoint fractional cost."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoullicommonendpointcharge-bernoulli-power-target-logarithmic-uniform-cost"),
                DeclarationHandle.Create(Prefix + "bernoulli_power_target_logarithmic_uniform_cost"),
                H("Uniform constants give a worst-world logarithmic cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For legal B,C,beta and moment order m, there are positive k and delta-zero, chosen before the seed law, error and stopping rule, such that every measurable seeded stopping time with the power-target accuracy contract has worst-window expected fractional endpoint cost at least k log(delta inverse)."))),
                DescribeRole.Theorem))));
}
