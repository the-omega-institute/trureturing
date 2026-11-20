using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AutomataCircuits;

internal sealed class LowAutomaticComplexityCircuitLowerBoundDocument : IScribeDocumentDefinition
{

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/chen2025lowautomaticcomplexity");
    private static DocumentBlock Node(string name, string id, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low automatic complexity and its complement defeat bounded-depth circuits.",
        H("Arbitrary-alphabet circuit lower bounds"), Blocks(
            Node("claim", "claim", "Question 5.1", Equal(Call("claim"), Body()),
                "Question 5.1, p. 19: “Do the results from Theorem 4.9 apply to arbitrary alphabets using the definition of ⊕SAC⁰ given in Definition 4.4?” Theorem 4.9 asserts both the Lq and complement lower bounds. Alphabet is an arbitrary finite type with at least two elements; q is rational with 0 < q < 1/2. The first conclusion proves that exact complexity is finite and attained. The remaining conclusions quantify over every prime-field alphabet embedding and every fixed injective Boolean block encoding. Original-symbol length is used in Lq. Constants are allowed, circuit size and addition fan-in are unrestricted, and correctness is required only on valid encoded words.", DescribeRole.Definition),
            Node("result", "result", "The affirmative arbitrary-alphabet result", Body(),
                "A repeated-factor estimate supplies sparse nonempty sections without a density assumption. If a word of length n has an exact k-state realization and no repeated m-factor, then n + 1 ≤ 2k + m². Low complexity therefore forces a repeated factor when m² ≤ (1 − 2q)n. The number of such length-n words over an r-letter alphabet is at most (n + 1)² r^(n−m). Choosing n proportional to m² makes this exponentially smaller than the whole section. The finite-grid polynomial obstruction then excludes each arithmetic circuit family. For Boolean encodings, restrict each block to two distinct alphabet letters and substitute their affine bit coordinates. This proves both language and complement conclusions at every rational threshold strictly between zero and one half. It asserts no endpoint q = 1/2 result, no growing-depth or growing-fan-in bound, and no separate density-limit theorem.", DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(X("Q")));
    private static Formula Ty() => X("Type");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(X(name))) : new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);

    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);


    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Inst(string cls, Formula type, Formula body) =>
        Seq(OpenBracket, Call(cls, type), CloseBracket, Comma, Sp, body);






    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));

    private static Formula FinOf(Formula n) => Call("Fin", n);


    private static Formula Card(Formula a) => App(Qualified("Fintype", "card"), a);
    private static Formula Compl(Formula a) => new Formula.Power(Parenthesized(a), X("c"));


    private static Formula Z(Formula p) => Call("ZMod", p);
    private static Formula Injective(Formula e) => App(Qualified("Function", "Injective"), e);
    private static Formula L(Formula a, Formula q) =>
        Call("Lq", Seq(X("Alphabet"), Sp, Colon, Eq, Sp, a), q);
    private static Formula OneHalf() => new Formula.Fraction(Cast(Num(1), Rat()), Num(2));


    private static Formula Body()
    {
        var a = X("Alphabet"); var q = X("q"); var p = X("p"); var e = X("e"); var t = X("t");
        var l = L(a, q);
        var arithmetic = All("p", N(), Implies(App(Qualified("Nat", "Prime"), p),
            All("e", Arrow(a, Z(p)), Implies(Injective(e),
                And(Not(Call("arithmeticRecognizable", p, e, l)),
                    Not(Call("arithmeticRecognizable", p, e, Compl(l))))))));
        var boolean = All("t", N(), All("e", Arrow(a, Arrow(FinOf(t), X("Bool"))),
            Implies(Injective(e), And(Not(Call("booleanRecognizable", t, e, l)),
                Not(Call("booleanRecognizable", t, e, Compl(l)))))));
        return All("Alphabet", Ty(), Inst("Fintype", a,
            Implies(LE(Num(2), Card(a)), And(Call("complexityTotal", a),
                All("q", Rat(), Implies(Less(Num(0), q), Implies(Less(q, OneHalf()),
                    And(arithmetic, boolean))))))));
    }
}
