using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class HadamardTruncatedBinomialLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit.";
    private const string SourceSentence = "Conjecture: H(x+1) = lim_{n->oo} n^{x+1} * Sum_{k=0..n} (-1)^k/(n+k) * binomial(x, k) such that H(1/4) = 0.79564036... . Changing the upper bound of the sum to oo yields Euler's product representation of the Gamma function.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Weil/ulgenes2026a398064");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The truncated binomial limit equals the entire Hadamard factorial function at every complex parameter.",
        H("Hadamard's truncated binomial limit"),
        Blocks(
            Node("hadamard", "IsHadamard", Disp(All("H", FunctionType(Complexes(), Complexes()),
                IffTo(Call("IsHadamard", F.Id("H")), HadamardBody(F.Id("H"))))),
                "The unpaginated COMMENT field of OEIS A398064, revision 39, states: \"The Hadamard function is an entire extension of the factorial function not equal to the gamma function. In other words, H(n) = (n-1)! for positive integers n.\" Here Differentiable over Complex expresses entire differentiability. The quotient specifies the function away from positive integers, where its factorial values give the removable continuation. The digamma quotient is the derivative form of Yin–Zhang equation (4.1).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("truncation", "truncation", Disp(All("x", Complexes(), All("n", Naturals(),
                Equal(Call("truncation", F.Id("x"), F.Id("n")), TruncationBody(F.Id("x"), F.Id("n")))))),
                "OEIS A398064, unpaginated FORMULA field, revision 39: \"" + SourceSentence + "\" The displayed finite sum is truncation x n. Ring.choose gives the generalized binomial coefficient; the exponential uses the real logarithm of n. Both k=0 and k=n are included. Natural indices are cast to Complex in the denominator and to Real before Real.log. Only positive n affect the limit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", Disp(IffTo(F.Id("claim"), ClaimBody())),
                "OEIS A398064, unpaginated FORMULA field, revision 39: \"" + SourceSentence + "\" The parameter x ranges over Complex, H maps Complex to Complex, and n tends to infinity through Naturals. Existence of the entire source function is asserted, followed by convergence for every function satisfying IsHadamard. The quoted decimal example and the statement about changing the upper limit to infinity are outside this proposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", Disp(ClaimBody()),
                "Euler's Gamma sequence supplies the scaled coefficient limit. On the left half-plane Re(x)<-1, a continuous weighted Riemann sum and two vanishing endpoints identify the limit with a Nielsen-beta integral. The digamma series identifies that integral, while a reciprocal-Gamma derivative construction supplies an entire factorial interpolation. The exact finite-sum shift and the interpolation's functional equation extend convergence to every complex parameter. The omitted infinite tail, convergence uniform in x, and altered cutoff ratios are separate questions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula HadamardBody(Formula h)
    {
        var m = F.Id("m");
        var y = F.Id("y");
        var first = Sub(D(1), Fraction(y, D(2)));
        var second = Fraction(Sub(D(1), y), D(2));
        return And(Call("Differentiable", Complexes(), h), And(
            All("m", Naturals(), Equal(Apply(h, Add(Cast(m, Complexes()), D(1))),
                Cast(Apply(Qualified("Nat", "factorial"), m), Complexes()))),
            All("y", Complexes(), ImpliesTo(
                Parenthesized(All("m", Naturals(), NeqTo(y, Add(Cast(m, Complexes()), D(1))))),
                Equal(Apply(h, y), Fraction(
                    Sub(Apply(Qualified("Complex", "digamma"), first), Apply(Qualified("Complex", "digamma"), second)),
                    Mul(D(2), Apply(Qualified("Complex", "Gamma"), Sub(D(1), y)))))))));
    }

    private static Formula TruncationBody(Formula x, Formula n)
    {
        var k = F.Id("k");
        var summand = Mul(Fraction(Power(Parenthesized(Negate(Cast(D(1), Complexes()))), k),
                Add(Cast(n, Complexes()), Cast(k, Complexes()))),
            Apply(Qualified("Ring", "choose"), x, k));
        return Mul(Apply(Qualified("Complex", "exp"),
                Mul(Parenthesized(Add(x, D(1))), Cast(Apply(Qualified("Real", "log"), Cast(n, Reals())), Complexes()))),
            Seq(Sum, Underscore, Grp(Bound("k", Apply(Qualified("Finset", "range"), Add(n, D(1))))), Sp, summand));
    }

    private static Formula ClaimBody() => And(
        Parenthesized(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("H"),
            FunctionType(Complexes(), Complexes()), Call("IsHadamard", F.Id("H")))),
        All("H", FunctionType(Complexes(), Complexes()), ImpliesTo(Call("IsHadamard", F.Id("H")),
            All("x", Complexes(), Call("Tendsto", Call("truncation", F.Id("x")),
                Qualified("Filter", "atTop"), Call("nhds", Apply(F.Id("H"), Add(F.Id("x"), D(1)))))))));

    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula FunctionType(Formula source, Formula target) => Parenthesized(Seq(source, To, target));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Bound(string name, Formula set) => Seq(F.Id(name), InMacro, set);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
