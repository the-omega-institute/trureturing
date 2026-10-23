using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class SeededBernoulliStoppedMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seeded Bernoulli stopping and a common endpoint budget.",
        H("Seeded Bernoulli stopping and a common endpoint budget"),
        Blocks(
            Paragraph(Text("For an arbitrary measurable seed space Seed and a seed probability measure nu, P(p)=nu times the iid Bernoulli(p) stream law on Seed times (Nat -> Bool). The seed law is independent of the parameter. Write X_i=1_{bit_i=true}-p, L(p0,p,k)=product_{i<k}[p/p0 if bit_i=true, else (1-p)/(1-p0)], and A(m)=((2^(2m+1)*(2m)^2)^m)*2^(2m). For t in WithTop Nat define T_n(t)=min(t,n), regarded as a natural number, and C_a(t)=t^a when finite and infinity at top. Put w(a,m,j)=(2^(a-m))^j and H(a,m)=2^a/(2^a-1)+(1-2^(a-m))^(-1). Expectations without a superscript are real Bochner integrals; nonnegative extended expectations allow infinite values.")),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-seededfiltration"),
                DeclarationHandle.Create(Prefix + "seededFiltration"),
                H("The seed and acquired prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every measurable Seed, the filtration at time n is the measurable-space comap of (seed, restriction of the bit stream to indices i<n). Thus the entire private seed is available initially and exactly the first n bits are observed at time n. This definition fixes the filtration used by all stopping-time statements in this document."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-bernoulli-stopped-output-identity"),
                DeclarationHandle.Create(Prefix + "bernoulli_stopped_output_identity"),
                H("The density of a stopped observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every seed probability nu, p0 in (0,1), p in [0,1], natural-valued stopping time tau for the seeded filtration, and real f strongly measurable for the stopping-time sigma algebra, the integral of f under P(p) equals its integral under P(p0) tilted by ofReal(L(p0,p,tau)). No boundedness of tau or integrability assumption on f is added: the equality uses the totalized Bochner integral on both sides. This is the stopped likelihood change-of-measure identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-centered-bit-bound"),
                DeclarationHandle.Create(Prefix + "centered_bit_bound"),
                H("Every centered bit has magnitude at most one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every type Seed, p in [0,1], natural i and omega in Seed times the Boolean stream, |1_{omega.bit(i)=true}-p|<=1. No measurable structure or probability law is required."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-bernoulli-stopped-moment-bound"),
                DeclarationHandle.Create(Prefix + "bernoulli_stopped_moment_bound"),
                H("Local parameter changes preserve a random moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every seed probability nu, p0 in (0,1), p in [0,1], seeded stopping time tau bounded everywhere by n, and natural m>0, put lambda=(p-p0)/(p0(1-p0)). If |lambda| sqrt(n)<=(2A(m)+1)^(-1), then E_{P(p)}[tau^m] equals the corresponding integral under P(p0) tilted by ofReal(L(p0,p,tau)), and E_{P(p)}[tau^m]<=2 E_{P(p0)}[tau^m]. Both conclusions concern the same parameter-independent stopping rule and seed distribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-truncation-cast"),
                DeclarationHandle.Create(Prefix + "truncation_cast"),
                H("Truncation agrees with the WithTop minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every function M from Seed times the Boolean stream to WithTop Nat, every natural n and every omega, the WithTop cast of T_n(M(omega)) is min(M(omega),n), including M(omega)=top."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-truncation-stopping"),
                DeclarationHandle.Create(Prefix + "truncation_stopping"),
                H("A deterministic truncation remains a stopping time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every WithTop-natural seeded stopping time M and natural n, omega -> T_n(M(omega)), cast to WithTop Nat, is a stopping time for the same seeded filtration."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-truncation-le"),
                DeclarationHandle.Create(Prefix + "truncation_le"),
                H("The deterministic truncation bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every t in WithTop Nat and natural n, T_n(t)<=n."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-truncated-moment-integrable"),
                DeclarationHandle.Create(Prefix + "truncated_moment_integrable"),
                H("Every bounded integer moment is integrable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every measurable space Omega, finite measure mu, measurable M:Omega -> WithTop Nat, and naturals n,m, omega -> (T_n(M(omega)))^m is Bochner integrable under mu. This includes n=0 and m=0."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-truncation-tail-bound"),
                DeclarationHandle.Create(Prefix + "truncation_tail_bound"),
                H("A truncated moment pays its own tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every measurable space Omega, measure mu, measurable M:Omega -> WithTop Nat, and naturals n,m, ofReal(n^m) times mu{n<M} is at most the nonnegative extended integral of ofReal(T_n(M)^m). No finite-measure hypothesis is required."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-endpoint-budget-finite"),
                DeclarationHandle.Create(Prefix + "endpoint_budget_finite"),
                H("Finite dyadic moments share one endpoint cost"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every measurable space Omega, measure mu, measurable M:Omega -> WithTop Nat, real a>0, natural m with a<m, and natural K, sum_{j<K} ofReal(w(a,m,j)) E_mu^+[ofReal(T_{2^j}(M)^m)] <= ofReal(H(a,m)) E_mu^+[C_a(M)]. The right side uses the same M for every j, and may be infinite."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-stopped-like-measurable"),
                DeclarationHandle.Create(Prefix + "stopped_like_measurable"),
                H("A likelihood at a measurable time is measurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every measurable Seed, p0,p in [0,1], and measurable tau:Seed times the Boolean stream -> Nat, omega -> L(p0,p,tau(omega)) is measurable."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-bernoulli-common-endpoint-budget"),
                DeclarationHandle.Create(Prefix + "bernoulli_common_endpoint_budget"),
                H("All local laws are charged to the same endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every seed probability nu, p0 in (0,1), sequence p(j) in [0,1], seeded WithTop-natural stopping time M, real a>0 and natural m with a<m, assume |(p(j)-p0)/(p0(1-p0))| sqrt(2^j)<=(2A(m)+1)^(-1) for every j. Five conclusions hold simultaneously. First, for every j, E_{P(p(j))}[T_{2^j}(M)^m]<=2E_{P(p0)}[T_{2^j}(M)^m]. Second, ofReal((2^j)^m) P(p(j)){2^j<M}<=2 E_{P(p0)}^+[ofReal(T_{2^j}(M)^m)]. Third, the infinite sum of the endpoint truncated moments weighted by ofReal(w(a,m,j)) is at most ofReal(H(a,m)) E_{P(p0)}^+[C_a(M)]. Fourth, for every extended nonnegative K, if E_{P(p(j))}^+[C_a(M)]<=K for every j, then E_{P(p0)}^+[C_a(M)]<=K. Fifth, the infinite sum of ofReal(w(a,m,j)) ofReal((2^j)^m) P(p(j)){2^j<M} is at most 2 ofReal(H(a,m)) E_{P(p0)}^+[C_a(M)]. The endpoint transfer uses the convergence of the local parameter laws and finite truncations; it does not replace the common stopping rule by independently chosen rules."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seededbernoullistoppedmoment-bernoulli-stopped-score-moment"),
                DeclarationHandle.Create(Prefix + "bernoulli_stopped_score_moment"),
                H("The centered stopped score retains the time moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/williams1991martingales")),
                Blocks(Paragraph(Text("For every seed probability nu, p0 in (0,1), seeded natural-valued stopping time tau bounded everywhere by n, and natural m>0, E_{P(p0)}^+[ofReal(|sum_{i<tau} X_i|^(2m))] <= ofReal(2A(m) E_{P(p0)}[tau^m]). No local parameter window is required for this centered-score estimate."))),
                DescribeRole.Theorem))));
}
