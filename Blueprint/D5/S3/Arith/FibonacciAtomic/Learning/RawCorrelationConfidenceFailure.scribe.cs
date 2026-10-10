using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Learning;

internal sealed class RawCorrelationConfidenceFailureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationConfidenceFailure.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static DocumentBlock Node(string name, string heading, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("raw-confidence-" + name.Replace('.', '-')),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw correlation on actual heterogeneous complete records has strict misordering "
            + "probability tending to one half at every fixed target-scale constant.",
        H("Failure of Uniform Raw-Correlation Confidence"),
        Blocks(
            Paragraph(Text("Use the four-window law, actual priority teachers and label channel "
                + "of RawCorrelationMomentIdentities. Every training record contains all "
                + "four windows and its label, and records are independent with the same "
                + "complete-record law. Fix 0<a<=1 and K>0, and let m=ceil(K/(a^2 rho^2)). "
                + "For each of the four increasing triples, its raw score is the sum of "
                + "(Y-1) times its actual teacher class over the m records. The true triple "
                + "is (1,3,4); the comparison triple is (2,3,4).")),
            Node("LazyLimit.tie_vanishes", "Conditional ties vanish",
                Seq(Call("tie", V("p"), V("m")), To, D(0)),
                "After excluding the reverse event independently in every record, the "
                    + "score difference has masses p/2,1-p,p/2 at -1,0,1. Its full "
                    + "product law is represented by independent activation bits and fair "
                    + "signs. The exact tie mixture averages the fair-sign tie coefficient "
                    + "at the activation count. Every fixed-count lower tail vanishes "
                    + "and the fair-sign tie coefficient tends to zero, so this mixture "
                    + "also tends to zero as rho decreases to zero."),
            Node("RawLimit.raw_confidence_failure", "Strict raw misordering has a half-probability limit",
                Seq(Call("P", Seq(Call("rawTrue"), Lt, Call("rawRival"))), To, Half),
                "For every fixed 0<a<=1 and K>0, the probability that the true raw score "
                    + "is strictly below the rival raw score tends to 1/2 as rho decreases "
                    + "to zero. Conditional symmetry gives (1-tie)/2. The difference "
                    + "between the conditional and original event probabilities is at "
                    + "most 1-(1-12 rho^3)^m, which tends to zero."),
            Node("Selection.failure_liminf", "Every deterministic maximizer has failure lower limit at least one half",
                Seq(Half, Le, Call("liminf", Call("failureMass"))),
                "For every family of selection functions, possibly depending on rho, "
                    + "which returns a maximum raw score among all four increasing triples "
                    + "at every sample, the failure probability has lower limit at least "
                    + "1/2. Ties may be resolved arbitrarily. Strict misordering already "
                    + "excludes the true teacher from every maximum."),
            Node("RandomSelection.failure_liminf", "The same bound holds for arbitrary randomized tie breaking",
                Seq(Half, Le, Call("liminf", Call("randomFailureMass"))),
                "The selection kernel assigns nonnegative candidate masses summing to "
                    + "one at each sample and is supported on maximum-score candidates. "
                    + "It may depend on rho and on the whole sample. Its probability of "
                    + "not returning the true teacher has lower limit at least 1/2."),
            Node("result", "Population moments and the uniform-confidence obstruction",
                Seq(Forall, Sp, V("a"), Comma, Sp, V("K"), Comma, Sp,
                    D(0), Lt, V("a"), Le, D(1), Sp, Land, Sp, D(0), Lt, V("K"),
                    Sp, Implies, Sp, Call("actualConfidenceObstruction", V("a"), V("K"))),
                "The combined statement includes legality for every 0<rho<=1/8, the "
                    + "pointwise difference and all five actual-law moment relations, the "
                    + "strict-misordering limit, and both deterministic and randomized "
                    + "maximum-score failure bounds. All these clauses use the same "
                    + "complete-record mass and sample count."),
            Paragraph(Text("The conclusion concerns finite-sample confidence despite a "
                + "positive population score gap. It does not assert reversed population "
                + "ordering or an optimal raw-score sample exponent. The symmetric random "
                + "walk tie formula and central-binomial decay are classical; the "
                + "complete-window law, exclusion event and target-scale limit fix the "
                + "specific application here.")))));
}
