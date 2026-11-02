using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class NoncompactQuantileDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Law => Call("ProbabilityMeasure", Real);
    private static Formula Joint => Call("ProbabilityMeasure", Seq(Real, Times, Real));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Bins(string m, Formula n) => Call("BinLaw", V(m), n);
    private static Formula Next => Seq(V("n"), Plus, D(1));
    private static Formula Tail(Formula m, Formula r) => Call("Tail", m, r);
    private static Formula Bound(string h) => Seq(Exists, Sp, V("M"), Colon, Sp, Real,
        Comma, Sp, All("x", Real), Bar, Call("apply", V(h), V("x")), Bar, Sp, Leq, Sp, V("M"));
    private static Formula Test(string regularity) => Seq(All("h", Fn(Real, Real)),
        Call(regularity, V("h")), Sp, Rightarrow, Open, Bound("h"), Close, Sp, Rightarrow,
        Call("DisplacementIntegral", V("h"), V("pi")), Eq, D(0));

    private static Formula Tails() => Disp(new Formula.Aligned([
        Seq(All("mu", Law), Call("IntegrableIdentity", V("mu")), Sp, Rightarrow,
            All("n", Nat), D(0), Lt, V("n"), Sp, Rightarrow,
            All("R", Real), D(0), Sp, Leq, Sp, V("R"), Sp, Rightarrow),
        Seq(Tail(Bins("mu", V("n")), V("R")), Sp, Leq, Sp, D(2),
            Tail(V("mu"), Seq(V("R"), Slash, D(2))))
    ]));

    private static Formula Approximation() => Disp(new Formula.Aligned([
        Seq(All("mu", Law), All("nu", Law), Call("IntegrableIdentity", V("mu")),
            Sp, Rightarrow, Call("IntegrableIdentity", V("nu")), Sp, Rightarrow),
        Seq(Call("Mean", V("mu")), Eq, Call("Mean", V("nu")), Sp, Rightarrow,
            Open, All("z", Real), Call("StopLoss", V("mu"), V("z")), Sp, Leq, Sp,
            Call("StopLoss", V("nu"), V("z")), Close, Sp, Rightarrow),
        Seq(Exists, Sp, V("piSeq"), Colon, Sp, Fn(Nat, Joint), Comma, Sp,
            Open, All("n", Nat), Call("IsMartingaleCoupling", Bins("mu", Next), Bins("nu", Next),
                Call("apply", V("piSeq"), V("n"))), Close),
        Seq(Land, Sp, Call("WeakLimit", Seq(V("n"), Mapsto, Bins("mu", Next)), V("mu")),
            Sp, Land, Sp, Call("WeakLimit", Seq(V("n"), Mapsto, Bins("nu", Next)), V("nu"))),
        Seq(Land, Sp, All("epsilon", Real), D(0), Lt, V("epsilon"), Sp, Rightarrow,
            Exists, Sp, V("R"), Colon, Sp, Real, Comma, Sp, D(0), Lt, V("R"), Sp, Land, Sp,
            All("n", Nat), Call("CoordinateTail", D(1), V("R"), Call("apply", V("piSeq"), V("n"))),
            Plus, Call("CoordinateTail", D(2), V("R"), Call("apply", V("piSeq"), V("n"))),
            Lt, V("epsilon"))
    ]));

    private static Formula Extension() => Disp(new Formula.Aligned([
        Seq(All("pi", Joint), Call("IntegrableCoordinate", D(1), V("pi")), Sp, Rightarrow,
            Call("IntegrableCoordinate", D(2), V("pi")), Sp, Rightarrow),
        Seq(Open, Test("Continuous"), Close, Sp, Rightarrow, Open, Test("Measurable"), Close)
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Synchronized conditional means of quantiles approximate integrable real laws while preserving discrete convex order and genuine absolute first-moment tails.",
        H("Integrable equal-quantile-bin approximation"),
        Blocks(
            Paragraph(Text("For a Borel probability law mu with integrable identity, let Q_mu be its generalized quantile. For positive integer n and k in Fin n, put a(mu,n,k)=n times the integral of Q_mu over (k/n,(k+1)/n]. BinLaw(mu,n) is the actual uniform finite probability law assigning weight 1/n to these n means. Repeated atoms are allowed. Tail(rho,R) denotes the integral of |x| over |x|>R against rho. CoordinateTail(i,R,pi) is the corresponding absolute ith-coordinate tail of the actual joint law. The same n is used for both marginals; no law is clipped or independently renormalized.")),
            Describe.Lean(DescribeId.Create("integrable-bin-absolute-tail"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NoncompactQuantile.absolute_tail_le"),
                H("Absolute tails of every bin-mean law"), StatementSource.FromAuthor(Tails()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("On a bin of mass 1/n, the absolute mean times 1/n is at most the integral of |Q_mu|. Split |Q_mu| at R/2. The portion below that threshold contributes at most R/(2n). If the absolute mean exceeds R, this contribution is less than half the absolute-mean contribution. Thus the latter is at most twice the remaining bin tail. Sum over the disjoint bins and apply the exact quantile pushforward identity. Integrability of the original absolute value then makes these bounds vanish uniformly over every positive resolution."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integrable-synchronized-martingale-approximations"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NoncompactQuantile.exists_martingale_approximations"),
                H("Actual finite martingale joints with converging marginals"),
                StatementSource.FromAuthor(Approximation()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/leskela2017conditionalconvex")),
                Blocks(
                    Paragraph(Text("Mean(rho) is the integral of the identity and StopLoss(rho,z) is the integral of max(x-z,0). IsMartingaleCoupling denotes both exact pushforward marginals, integrability of both joint coordinates, and zero displacement integrals for every bounded measurable first-coordinate test. WeakLimit denotes convergence in the weak topology of probability measures. The conclusion chooses one sequence of actual finite joint laws and asserts the two marginal convergences and a single uniform sum-of-coordinate-tails criterion.")),
                    Paragraph(Text("Quantile integrability follows from the original law by its pushforward identity. Each bin mean is monotone in its bin index, and the sum through bin K is n times the integral of Q_mu over (0,(K+1)/n]. Equal means and the stop-loss inequalities give reversed lower integrated-quantile inequalities. Finite majorization therefore orders both lists of bin means, and the existing uniform finite martingale-coupling construction produces the actual joint laws.")),
                    Paragraph(Text("At every continuity point in (0,1), the bin containing that point shrinks to it, and its average converges to the quantile value. Monotone quantiles have only countably many discontinuities. Dominated convergence for bounded continuous tests gives weak convergence of the finite laws. The absolute-tail bound gives uniform integrability separately, and the exact marginal identities transfer it to each actual joint. No density, nonatomicity, common compact interval or filtration-generation assumption is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integrable-martingale-test-extension"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NoncompactQuantile.tested_measurable_of_continuous"),
                H("From bounded continuous tests to bounded measurable tests"),
                StatementSource.FromAuthor(Extension()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/lyng2026compactstrassen")),
                Blocks(
                    Paragraph(Text("DisplacementIntegral(h,pi) is the integral of (y-x)h(x) against pi. Bound means the existence of one real bound for the absolute value of h at every real argument. Both coordinate-integrability hypotheses concern this same joint law. The premise quantifies over every continuous bounded h; the conclusion quantifies over every Borel measurable bounded h.")),
                    Paragraph(Text("Weight the joint law by the positive and negative parts of y-x and project each finite weighted measure through the first coordinate. Vanishing continuous displacement tests identify these two finite measures by bounded-continuous extensionality. Their equality then gives the identity for every bounded measurable test. This is the shared weighted-measure argument used by the compact and integrable constructions."))),
                DescribeRole.Theorem))));
}
