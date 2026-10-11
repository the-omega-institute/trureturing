using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class MovingSupportKLTransportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/DivergenceSupport/MovingSupportKLTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-record likelihood ratios control posterior KL losses uniformly over changing supports.",
        H("Moving-support posterior KL transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("posterior-defect"),
                DeclarationHandle.Create(Owner + "posteriorDefect"),
                H("Posterior loss on actual positive records"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite hidden and coarse state spaces J and I, two real mass functions " +
                    "d and q on J, a common record channel W from J to an arbitrary record space H, " +
                    "and a coarse map r from J to I, posteriorDefect at record h is the KL " +
                    "divergence between the two Bayes posteriors minus the KL divergence between " +
                    "their r-pushforwards. This expression is used only when the actual record " +
                    "mass D(h) is positive. On actual null records the scalar loss is zero. " +
                    "Zero posterior coordinates and disappearing coarse fibers are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("posterior-defect-lone-transport"),
                DeclarationHandle.Create(Owner + "posterior_defect_l1_of_ae_tendsto"),
                H("Uniform tail transport and convergence in L1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let J and I be finite, let H(n) be a finite measurable record space " +
                        "with measurable singletons for each natural n, and let mu be one " +
                        "probability measure on a measurable space Omega. Each measurable " +
                        "record map from Omega to H(n) has actual singleton masses " +
                        "D(n,h) = sum_j d(j) W(n,j,h). The common nonnegative channels W(n) " +
                        "have unit row sums. The prior d is nonnegative and normalized, " +
                        "q is strictly positive and normalized, and d(j) is at most M q(j) " +
                        "for one positive constant M and every j. The map r is arbitrary; " +
                        "in particular it may be the surjective coarse label.")),
                    Paragraph(Text(
                        "Write Q(n,h) = sum_j q(j) W(n,j,h), let f(n) be posteriorDefect " +
                        "evaluated on the nth record, and set U(n) to log(M/(D(n)/Q(n))) " +
                        "on positive actual records and to zero otherwise. For every " +
                        "nonnegative v, mu(U(n) > v) is at most M exp(-v), uniformly in n. " +
                        "For every nonnegative R, the integral of f(n) over f(n) >= R is " +
                        "at most M (R+1) exp(-R), again uniformly in n.")),
                    Paragraph(Text(
                        "If f(n) converges almost everywhere to a real function g, then " +
                        "the family f is uniformly integrable, g is integrable, the L1 " +
                        "seminorm of f(n)-g tends to zero, and the integrals of f(n) tend " +
                        "to the integral of g. The record mass identity and the almost " +
                        "everywhere limit are hypotheses of this transport theorem. " +
                        "Independence of the mixed records and a fixed positive lower " +
                        "bound on posterior coordinates are not required.")),
                    Paragraph(Text(
                        "The finite data-processing inequality gives nonnegativity and " +
                        "the prior density bound gives f(n) <= U(n). The identity " +
                        "D = Q M exp(-U) transports actual tail contributions to reference " +
                        "mass. The scalar inequality u exp(-u) <= (R+1) exp(-R) for u >= R " +
                        "bounds their sum. This is an estimate of a family of random " +
                        "losses, rather than a uniform deterministic bound on each loss. " +
                        "The quantitative tail estimate supplies the uniform-integrability " +
                        "hypothesis of the L1 convergence theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-support-posterior-limit"),
                DeclarationHandle.Create(Owner + "moving_support_posterior_limit"),
                H("Posterior coordinate limits across disappearing supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Keep the common finite-record model and prior density bound of the " +
                        "preceding theorem. Let a and b be real coordinate families on Omega " +
                        "times J, and let t be a real function on Omega. Almost everywhere, " +
                        "assume that D(n)/Q(n) tends to the positive number t and that the actual and " +
                        "reference posterior coordinates tend respectively to a and b, " +
                        "simultaneously for every hidden state. Positivity of every actual " +
                        "finite-record mass holds almost everywhere by its prescribed law.")),
                    Paragraph(Text(
                        "The posterior loss then tends almost everywhere to " +
                        "KL(a,b)-KL(r_*a,r_*b). The losses are uniformly integrable; " +
                        "this limit is integrable; convergence holds in L1; and the " +
                        "expectations converge to the expectation of this limit. " +
                        "No coordinate of b, or of its coarse pushforward, is required " +
                        "to be positive.")),
                    Paragraph(Text(
                        "Along each such path the posterior density ratio is eventually " +
                        "bounded by 2M/t. If a reference coordinate tends to zero, its " +
                        "KL summand equals that reference coordinate times x log(x), " +
                        "with x in a bounded nonnegative interval. Continuity of " +
                        "x log(x), including its zero value, makes this summand vanish. " +
                        "The same argument applies after grouping coordinates into " +
                        "coarse fibers. Finite summation gives the almost everywhere " +
                        "loss limit, and common-record tail transport upgrades it to L1. " +
                        "Identifying a and b with the conditional priors of an iid " +
                        "observation-row class remains a separate hypothesis-supplying step."))),
                DescribeRole.Theorem))));
}
