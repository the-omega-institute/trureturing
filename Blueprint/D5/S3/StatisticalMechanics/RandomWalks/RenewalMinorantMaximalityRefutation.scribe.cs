using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.RandomWalks;

internal sealed class RenewalMinorantMaximalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/RandomWalks/RenewalMinorantMaximalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/nikolovsavov2024renewal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nikolov and Savov's Conjecture 3.7 fails at k = 4: the polynomial x^2(x+y+z)+xy is a degree-three renewal minorant strictly above Q_4 at interior points of the probability simplex.",
        H("Q_4 is not a maximal renewal minorant"),
        Blocks(
            Node("Ak", "The probability simplex", AkFormula(),
                "Equation (2.6), p. 3: \"A_k = {(p_1, ···, p_{k−1}) : p_l ≥ 0, 1 ≤ l ≤ k − 1; ∑_{l=1}^{k−1} p_l ≤ 1} ⊆ R^{k−1}.\" Coordinates are indexed by Fin(k−1): coordinate i represents the source's p_(i+1). Natural-number subtraction in Fin(k−1) is truncated subtraction. The claim uses only k ≥ 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stepMass", "The step distribution", StepMassFormula(),
                "Section 2, p. 2: \"P(X_1 = l) = p_l ≥ 0, 1 ≤ l ≤ k, and ∑_{l=1}^k p_l = 1.\" \"Extend p_n = 0 for n ≥ k + 1.\" The first k−1 coordinates determine p_k = 1 − ∑_{l<k} p_l. The displayed ite is if-then-else; p_(l−1) is the Fin(k−1) coordinate formed from the natural number l−1 when 1 ≤ l < k. The value at l = 0 is outside the recurrence for k ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("renewal", "The renewal recurrence", RenewalFormula(),
                "Equation (2.2), p. 2: \"Obviously u_0 = 1 and the well-known recurrent relation holds u_n = ∑_{l=1}^n p_l u_{n−l} = ∑_{l=1}^{min{n,k}} p_l u_{n−l}.\" Here u_n = renewal(p,n). The Fin(min(n+1,k)) index l denotes the source's step l+1; val exposes its natural-number value. The difference of time indices is natural-number truncated subtraction, agreeing with ordinary subtraction on the summation range.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("polynomialLE", "The pointwise polynomial ordering", PolynomialLEFormula(),
                "Section 2, p. 3: \"We set P_k for the set of polynomials of k − 1 variables. We introduce partial ordering in P_k in the following manner: we say that P_1 ≺ P_2, P_1, P_2 ∈ P_k, if and only if P_1 ≤ P_2 on A_k.\" P_k is MvPolynomial(Fin(k−1), R) with real coefficients, and polynomialLE is this non-strict ordering.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("minorantClass", "The class of polynomial minorants", MinorantClassFormula(),
                "Equations (2.4) and (2.7), pp. 2–3: \"M_k = max_{l≥1}{u_l} and m_k = min_{l≥1}{u_l}.\" \"𝒜_k := {P ∈ P_k : deg(P) ≤ k − 1, P ≺ m_k},\" where \"deg(P) is the power of P, i.e. the highest combined power of every monomial constituting P.\" Degree is totalDegree. P ≺ m_k is encoded as eval(p,P) ≤ u_n for every p in A_k and every n ≥ 1; this lower-bound formulation does not assume attainment of a minimum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Q", "The product of partial sums", QFormula(),
                "Equation (2.5), p. 2: \"Q_n(p_1, p_2, ···, p_{n−1}) = ∏_{j=1}^{n−1} ∑_{l=1}^j p_l.\" The empty product is 1. Q(k) is the corresponding polynomial in the variables X_l indexed from zero; the inner sum selects l ≤ j. The displayed ite is if-then-else.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The maximality clause of Conjecture 3.7", ClaimDefinitionFormula(),
                "Conjecture 3.7, p. 5: \"For any k ≥ 3, Q_k is a maximal element in 𝒜_k and it is largest in 𝒜̂_k.\" Equation (2.8), p. 3: \"We say that P ∈ 𝒜_k is maximal if and only if P̃ ∈ 𝒜_k and P̃ ≻ P ⇒ P̃ = P.\" The claim encodes the first clause with polynomial equality and the pointwise non-strict order. Conjecture 3.7 implies claim, so ¬ claim refutes the conjecture. The separate hatted class is not used.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation at k = 4", Disp(new Formula.Not(F.Id("claim"))),
                "Write x=p_1, y=p_2, z=p_3 and w=1−x−y−z. Set P=x^2(x+y+z)+xy. Then P−Q_4=xyw ≥ 0 on A_4. Its degree is at most 3, and it differs from Q_4: at x=y=z=w=1/4 the values are P=7/64 and Q_4=6/64. The initial renewal masses are u_1=x, u_2=x^2+y and u_3=x^3+2xy+z. The certificates u_1−P=x(z+(1+x)w), u_2−P=x^2w+y(1−x), and u_3−P=xy(1−x)+z(1−x^2) are nonnegative on A_4. Also P ≤ u_1 ≤ 1=u_0. For n ≥ 4 the recurrence is a convex combination of the preceding four masses, so strong induction gives P ≤ u_n for every positive n. Thus P belongs to 𝒜_4 and contradicts maximality of Q_4.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nikolov-savov-2023-renewal-minorant-maximality-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("renewal-minorant-" + (declaration switch
            {
                "Ak" => "ak", "stepMass" => "step-mass", "polynomialLE" => "polynomial-le",
                "minorantClass" => "minorant-class", "Q" => "q", _ => declaration,
            })),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Index(Formula k) => Call("Fin", Subtract(k, D(1)));
    private static Formula Coordinates(Formula k) => new Formula.TypeArrow(Index(k), Reals());
    private static Formula Polynomials(Formula k) => Call("MvPolynomial", Index(k), Reals());
    private static Formula SumOver(string v, Formula type, Formula value) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(v), Colon, type)), Sp, value);
    private static Formula SetOf(string v, Formula type, Formula predicate) =>
        Seq(OpenBrace, F.Id(v), Colon, type, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula AkFormula()
    {
        Formula k=F.Id("k"), p=F.Id("p"), i=F.Id("i");
        return Disp(All("k", Naturals(), Equal(Call("Ak", k), SetOf("p", Coordinates(k),
            And(All("i", Index(k), AtMost(D(0), App(p,i))),
                AtMost(SumOver("i", Index(k), App(p,i)), D(1)))))));
    }

    private static Formula StepMassFormula()
    {
        Formula k=F.Id("k"), p=F.Id("p"), l=F.Id("l"), i=F.Id("i");
        Formula value=Call("ite", Parenthesized(And(AtMost(D(1),l),Less(l,k))),
            new Formula.Subscript(p, Subtract(l,D(1))),
            Call("ite", Parenthesized(Equal(l,k)), Subtract(D(1),SumOver("i",Index(k),App(p,i))),D(0)));
        return Disp(All("k",Naturals(),All("p",Coordinates(k),All("l",Naturals(),
            Equal(Call("stepMass",p,l),value)))));
    }

    private static Formula RenewalFormula()
    {
        Formula k=F.Id("k"), p=F.Id("p"), n=F.Id("n"), l=F.Id("l");
        Formula step=Add(Call("val",l),D(1));
        Formula sum=SumOver("l",Call("Fin",Call("min",Add(n,D(1)),k)),
            Mul(Call("stepMass",p,step),Call("renewal",p,Subtract(Add(n,D(1)),step))));
        Formula zero=All("k",Naturals(),All("p",Coordinates(k),Equal(Call("renewal",p,D(0)),D(1))));
        Formula next=All("k",Naturals(),All("p",Coordinates(k),All("n",Naturals(),
            Equal(Call("renewal",p,Add(n,D(1))),sum))));
        return Disp(new Formula.Aligned([zero,next]));
    }

    private static Formula PolynomialLEFormula()
    {
        Formula k=F.Id("k"), p=F.Id("p"), P=F.Id("P"), R=F.Id("R");
        return Disp(All("k",Naturals(),All("P",Polynomials(k),All("R",Polynomials(k),
            IffOf(Call("polynomialLE",P,R),All("p",Coordinates(k),
                Implies(Member(p,Call("Ak",k)),AtMost(Call("eval",p,P),Call("eval",p,R)))))))));
    }

    private static Formula MinorantClassFormula()
    {
        Formula k=F.Id("k"), p=F.Id("p"), P=F.Id("P"), n=F.Id("n");
        Formula lower=All("p",Coordinates(k),Implies(Member(p,Call("Ak",k)),
            All("n",Naturals(),Implies(AtMost(D(1),n),AtMost(Call("eval",p,P),Call("renewal",p,n))))));
        return Disp(All("k",Naturals(),Equal(Call("minorantClass",k),SetOf("P",Polynomials(k),
            And(AtMost(Call("totalDegree",P),Subtract(k,D(1))),lower)))));
    }

    private static Formula QFormula()
    {
        Formula k=F.Id("k"), l=F.Id("l"), j=F.Id("j");
        Formula sum=SumOver("l",Index(k),Call("ite",Parenthesized(AtMost(l,j)),Call("X",l),D(0)));
        Formula product=Seq(new Formula.Subscript(Prod,Seq(j,Colon,Index(k))),Sp,Parenthesized(sum));
        return Disp(All("k",Naturals(),Equal(Call("Q",k),product)));
    }

    private static Formula ClaimBody()
    {
        Formula k=F.Id("k"), P=F.Id("P"), q=Call("Q",k), cls=Call("minorantClass",k);
        Formula maximal=All("P",Polynomials(k),Implies(Member(P,cls),
            Implies(Call("polynomialLE",q,P),Equal(P,q))));
        return All("k",Naturals(),Implies(AtMost(D(3),k),And(Member(q,cls),maximal)));
    }
    private static Formula ClaimDefinitionFormula() => Disp(IffOf(F.Id("claim"),ClaimBody()));
}
