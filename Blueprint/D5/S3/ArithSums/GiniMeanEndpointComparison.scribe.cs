using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class GiniMeanEndpointComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/GiniMeanEndpointComparison.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/grunwaldpales2024gini");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-point rational witness refutes endpoint characterization of Gini mean comparisons.",
        H("Endpoint comparison of Gini means on a bounded interval"),
        Blocks(
            SourceQuotation(),
            Entry("gini-mean", "giniMean", "The distinct-parameter Gini mean", GiniMean(),
                "For x : Fin n → ℝ, giniMean r s x is the displayed real-power expression. "
                + "For positive coordinates and r≠s it is the source's Gini mean. The Lean definition is "
                + "a total real-valued expression; the equal-parameter mean is not encoded.",
                DescribeRole.Definition, true),
            Entry("low-tuple", "lowTuple", "One upper endpoint", LowTuple(),
                "The index i ranges over Fin n. The value val i is its natural-number index. "
                + "The tuple places b at the last index and a elsewhere, so for n=3 it is (a,a,b).",
                DescribeRole.Definition, false),
            Entry("high-tuple", "highTuple", "One lower endpoint", HighTuple(),
                "The tuple places a at index zero and b elsewhere, so for n=3 it is (a,b,b). "
                + "Both tuple definitions also apply to n=0, when there are no indices.",
                DescribeRole.Definition, false),
            Entry("endpoint-claim", "claim", "Sufficiency of the two extreme endpoint tests", Claim(),
                "The claim is the proposed ⊇ inclusion of Conjecture 1 for closed intervals [a,b] "
                + "and distinct parameters r≠s and p≠q. It quantifies over n≥3 and 0<a<b. "
                + "The parameter-sum inequality and both endpoint comparisons are required to imply "
                + "comparison at every tuple whose coordinates lie in [a,b]. This restricted implication "
                + "is enough to refute the full conjectured equality.",
                DescribeRole.Definition, false),
            Entry("refutation", "result", "The extreme endpoint tests are insufficient", Disp(Seq(Neg, Sp, V("claim"))),
                "Take n=3, a=1, b=3, (r,s)=(3,−1), and (p,q)=(0,2). Both parameter sums equal 2. "
                + "The lemmas gini_low_rs and gini_low_pq give fourth powers 87/7 and 121/9 at (1,1,3). "
                + "The lemmas gini_high_rs and gini_high_pq give 33 and 361/9 at (1,3,3). "
                + "The nonnegativity lemmas and le_fourth establish both endpoint comparisons. "
                + "The private tuple x=(1,1,5/3) has all coordinates in [1,3]. The lemmas gini_x_rs "
                + "and gini_x_pq give fourth powers 895/351 and 1849/729 there. Their order reverses: "
                + "895·729=652455>648999=1849·351. Applying the claim to this tuple yields a false "
                + "fourth-power inequality. Thus the proposed ⊇ inclusion, and hence Conjecture 1, fails. "
                + "As mathematical reasoning, homogeneity scales x to (a,a,5a/3), an endpoint configuration "
                + "at a smaller ratio. For these parameters the comparison fails at ratio 5/3 but holds at "
                + "ratio 3, so the extreme ratio does not control the intermediate ratios. A candidate "
                + "correction requires both endpoint tests for every t∈(1,b/a]; its sufficiency is not proved. "
                + "Further integer-parameter violations, including (−2,0,4,−6) on [1,4] at (1,13/8,13/8), "
                + "are computed numerical observations and are not formalized. Conjecture 2 for inf I=0 "
                + "or sup I=∞, and the true bounded-interval description of Γn(I), are not settled by this result. "
                + "The journal version's text is ASSUMED-UNVERIFIED; the quotations refer to arXiv:2408.07658v1, §4.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Grünwald and Páles, Comparison of Gini means with fixed number of variables, arXiv:2408.07658v1, "
        + "§4, introductory paragraph, verbatim: “We conclude this paper by formulating two conjectures "
        + "that we have not been able to verify. The first conjecture seems to be a natural extension of "
        + "the formula for Γ2(I), if 0 < inf I < sup I < ∞.” Conjecture 1 states verbatim: “Conjecture 1. "
        + "Let n ≥ 3 and let I be a subinterval of R+ such that 0 < a := inf I < sup I =: b < ∞. "
        + "Then Γn(I) = {((r, s), (p, q)) ∈ R² × R² | r + s ≤ p + q, "
        + "G[n]r,s(a, …, a, b) ≤ G[n]p,q(a, …, a, b), and "
        + "G[n]r,s(a, b, …, b) ≤ G[n]p,q(a, b, …, b)}.”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("grunwald-pales-2024-gini-mean-comparison"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Fin => Call("Fin", V("n"));
    private static Formula Tuple => Seq(Fin, Sp, To, Sp, Real);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, Parenthesized(type), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula EqTo(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeTo(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeTo(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtTo(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula SumPowers(Formula exponent) =>
        Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Fin)), Sp,
            new Formula.Power(Call("x", V("i")), exponent));

    private static Formula GiniMean() => Disp(All("n", Natural, All("r", Real, All("s", Real,
        All("x", Tuple, EqTo(Call("giniMean", V("r"), V("s"), V("x")),
            new Formula.Power(Parenthesized(new Formula.Fraction(SumPowers(V("r")), SumPowers(V("s")))),
                new Formula.Fraction(D(1), Subtract(V("r"), V("s"))))))))));

    private static Formula LowTuple() => Disp(All("n", Natural, All("a", Real, All("b", Real,
        All("i", Fin, EqTo(Call("lowTuple", V("n"), V("a"), V("b"), V("i")),
            Call("ite", EqTo(Add(Call("val", V("i")), D(1)), V("n")), V("b"), V("a"))))))));

    private static Formula HighTuple() => Disp(All("n", Natural, All("a", Real, All("b", Real,
        All("i", Fin, EqTo(Call("highTuple", V("n"), V("a"), V("b"), V("i")),
            Call("ite", EqTo(Call("val", V("i")), D(0)), V("a"), V("b"))))))));

    private static Formula Comparison(Formula x) =>
        LeTo(Call("giniMean", V("r"), V("s"), x), Call("giniMean", V("p"), V("q"), x));

    private static Formula Claim()
    {
        Formula low = Call("lowTuple", V("n"), V("a"), V("b"));
        Formula high = Call("highTuple", V("n"), V("a"), V("b"));
        Formula coordinates = All("i", Fin,
            And(LeTo(V("a"), Call("x", V("i"))), LeTo(Call("x", V("i")), V("b"))));
        Formula conclusion = All("x", Tuple, Imp(coordinates, Comparison(V("x"))));
        Formula parameters = All("r", Real, All("s", Real, All("p", Real, All("q", Real,
            Imp(NeTo(V("r"), V("s")), Imp(NeTo(V("p"), V("q")),
                Imp(LeTo(Add(V("r"), V("s")), Add(V("p"), V("q"))),
                    Imp(Comparison(low), Imp(Comparison(high), conclusion)))))))));
        Formula endpoints = All("a", Real, All("b", Real,
            Imp(LtTo(D(0), V("a")), Imp(LtTo(V("a"), V("b")), parameters))));
        return Disp(IffTo(V("claim"), All("n", Natural, Imp(LeTo(D(3), V("n")), endpoints))));
    }
}
