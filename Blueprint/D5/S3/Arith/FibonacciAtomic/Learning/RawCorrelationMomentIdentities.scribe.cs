using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Learning;

internal sealed class RawCorrelationMomentIdentitiesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Pow(Formula x, byte n) => Seq(x, Caret, Grp(D(n)));
    private static Formula Sub(Formula x, byte n) => Seq(x, Underscore, Grp(D(n)));
    private static Formula All(string x, string type, Formula body) =>
        Seq(Forall, Sp, V(x), Colon, Sp, Call(type), Comma, Sp, body);
    private static Formula Positive(string x) => Seq(D(0), Lt, V(x));
    private static Formula AtScale(Formula body, bool bounded = true) => All("a", "Real", All("K", "Real",
        Seq(bounded ? Seq(Positive("a"), Le, D(1)) : Positive("a"), Sp, Land, Sp, Positive("K"),
            Sp, Implies, Sp, body)));
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);

    private static DocumentBlock Node(string name, string heading, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("raw-moments-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual four-window experiment has a positive raw-score mean but an increasing "
            + "number of conditionally symmetric nonzero score differences.",
        H("Actual Window Laws, Moments and Nonzero Counts"),
        Blocks(
            Paragraph(Text("The alphabet, in low-to-high bit order, is 000,100,010,101,001. "
                + "A record contains four complete windows and a label in {0,1,2}. "
                + "Window 1 has masses (rho,rho,rho,rho,1-4 rho); windows 2,3,4 have "
                + "masses ((1-3 rho)/2,rho,(1-3 rho)/2,rho,rho). Windows at different "
                + "positions are independent. The two endpoints inside window 3 belong to "
                + "that same window and retain their actual joint law.")),
            Paragraph(Text("The true teacher uses windows (1,3,4), and its competitor uses "
                + "(2,3,4). The priority teacher returns 1 when its first high-low gate is "
                + "open, otherwise 2 when its second gate is open, and 0 otherwise. Given "
                + "the true class c, the label is sampled from R_a=a R+(1-a)J/3, where "
                + "the rows of R are (1/2,1/4,1/4), (3/8,1/4,3/8), (1/4,1/4,1/2). "
                + "Z=Y-1 and score=Z(C_true-C_rival). The complete record mass is the "
                + "product of the four window masses and this conditional label mass. "
                + "The displayed limitCleanMass and limitCountTail denote limits as rho "
                + "decreases to zero, with m=ceil(K/(a^2 rho^2)); the latter uses the "
                + "conditional nonzero count and its displayed cutoff N.")),
            Node("Law.position_law_admissible", "Legal whole-window position laws",
                Seq(Forall, Sp, V("rho"), Comma, Sp, D(0), Lt, V("rho"), Le,
                    Seq(Frac, Grp(D(1)), Grp(D(8))), Sp, Implies, Sp,
                    Call("Admissible", V("rho"), Call("positionLaw", V("rho")))),
                "For every 0<rho<=1/8, each position law has total mass one and each of "
                    + "its five symbol masses is at least rho."),
            Node("Law.difference_formula", "The pointwise teacher difference",
                All("w", "Record", EqOf(Call("difference", V("w")), Seq(Open, Call("apply", Sub(V("h"), 1), V("w")), Minus, Call("apply", Sub(V("h"), 2), V("w")), Close,
                    Call("apply", Sub(V("l"), 3), V("w")), Open, D(1), Minus, D(2), Call("apply", Sub(V("h"), 3), V("w")), Call("apply", Sub(V("l"), 4), V("w")), Close))),
                "This identity holds for every complete record, including every label. "
                    + "Here hi and li are the high and low zero-one endpoint indicators, "
                    + "and D=C_true-C_rival. Both h3 and l3 refer to window 3."),
            Node("Law.actual_moments", "Five exact actual-law moments",
                All("rho", "Real", All("a", "Real",
                    Seq(Positive("rho"), Sp, Land, Sp, Positive("a"), Sp, Implies, Sp,
                    new Formula.Aligned([
                    EqOf(Call("disagreement", V("rho"), V("a")), Seq(D(2), V("rho"), Open, D(1), Minus,
                        D(5), V("rho"), Plus, D(1, 2), Pow(V("rho"), 2), Close)),
                    EqOf(Call("normGap", V("rho"), V("a")), Seq(Minus, D(2), V("rho"), Plus,
                        D(1, 0), Pow(V("rho"), 2))),
                    EqOf(Call("mean", V("rho"), V("a")), Seq(D(3), V("a"), Pow(V("rho"), 3))),
                    EqOf(Call("variance", V("rho"), V("a")), Seq(Call("kappa", V("a")), Call("disagreement", V("rho"), V("a")), Minus,
                        D(9), Pow(V("a"), 2), Pow(V("rho"), 6))),
                    Seq(D(0), Lt, Call("mean", V("rho"), V("a")))])))),
                "The identities are finite-sum identities for all rho>0 and a>0. For "
                    + "0<rho<=1/8 and 0<a<=1, the mass is a probability law: d is the "
                    + "expectation of D squared, normGap is the expectation of "
                    + "(C_true-1)^2-(C_rival-1)^2, mean is "
                    + "the expectation of score, variance is its second moment minus its "
                    + "squared mean, and kappa(a)=(8+a)/12. These formulas integrate the "
                    + "actual joint window-label mass, with no independent endpoint replacement."),
            Node("Law.all_clean_limit", "Simultaneous exclusion of the reverse event",
                AtScale(Seq(Call("limitCleanMass", V("a"), V("K")), Eq, D(1)), false),
                "For all fixed a>0 and K>0, put m=ceil(K/(a^2 rho^2)). The reverse event "
                    + "is h1=0,h2=1,l3=1. Its single-record mass is 12 rho^3. The "
                    + "probability that all m independent records avoid it is "
                    + "(1-12 rho^3)^m, which tends to one as rho decreases to zero."),
            Node("Law.nonzero_count_diverges", "Conditional nonzero counts escape every fixed cutoff",
                AtScale(All("N", "Nat", Seq(
                    Call("limitCountTail", V("a"), V("K"), V("N")), Eq, D(0)))),
                "Fix 0<a<=1 and K>0. Condition each complete record on avoiding the reverse "
                    + "event, and let Jm count records with nonzero score. For every natural "
                    + "cutoff N, P(Jm<=N) tends to zero as rho decreases to zero. The "
                    + "conditional nonzero mass is p=kappa(a) 2 rho(1-3 rho)(1-2 rho)/"
                    + "(1-12 rho^3), and m p tends to infinity. The finite-product "
                    + "Laplace transform gives the bound exp(N) exp(-(1-exp(-1)) m p)."),
            Paragraph(Text("Finite sums and product factorization are standard probability "
                + "algebra. The fair-sign tie coefficient is zero at odd lengths and "
                + "choose(j,j/2)/2^j at even lengths. The central-binomial estimate is "
                + "reused from Nat.choose_middle_sq_mul_le in the Gelfond module; it implies "
                + "that the tie coefficient tends to zero. These classical estimates "
                + "are applied to the specified complete-record experiment.")))));
}
