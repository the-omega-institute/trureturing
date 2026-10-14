using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class SunWeightedDistinctSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/SunWeightedDistinctSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/sun2021weighteddistinctsums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sun's weighted distinct-sum bound is refuted over the rationals at n = 2 by the set {0, 1, 2}.",
        H("Sun's weighted distinct-sum conjecture"),
        Blocks(
            Paragraph(Text(
                "Zhi-Wei Sun, \"On permutations of {1,...,n} and related topics\", J. Algebraic Combin. "
                    + "54 (2021) 893–912, Conjecture 4.9, page 18, states verbatim: \"Conjecture 4.9. Let n ∈ Z+ and let F be a field with p(F) > n + 1, where p(F) = p if the characteristic of F is a prime p, and p(F) = +∞ if the characteristic of F is zero. Let A be any finite subset of F with |A| ⩾ n + δ_{n,3}, where δ_{n,3} is 1 or 0 according as n = 3 or not. Then, for the set S(A) := {Σ_{k=1}^n k a_k : a_1, . . . , a_n are distinct elements of A} (4.8), we have |S(A)| ⩾ min{p(F), (|A| − n) n(n+1)/2 + n(n²−1)/6 + 1}. (4.9)\"")),
            Node("pf", "The characteristic bound", PFormula(),
                "The value pF F is top when ringChar F is zero and is the natural cast of ringChar F otherwise. "
                    + "This is the paper's p(F), with top representing +∞.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weighted", "Weighted distinct sums", WeightedFormula(),
                "For a finite set A in a field and a natural n, weightedDistinctSums A n is the image of all "
                    + "embeddings of Fin n into the subtype of A under the sum whose kth coefficient is k+1. "
                    + "The embeddings enforce that the selected elements are distinct members of A.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bound", "The numerical lower bound", BoundFormula(),
                "sunBound m n is the natural-number expression (m−n)n(n+1)/2 + n(n²−1)/6 + 1 from (4.9). "
                    + "Natural-number division is floor division.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 4.9", ClaimFormula(),
                "The displayed proposition is Conjecture 4.9 with the field, characteristic, cardinality and "
                    + "weighted-sum notation written explicitly. The source's δn,3 is encoded by the conditional "
                    + "if n = 3 then 1 else 0.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is false", ResultFormula(),
                "At F = ℚ, n = 2 and A = {0,1,2}, the six ordered pairs give the values 2, 4, 1, 5, 2, 4. "
                    + "Thus the distinct sums are {1,2,4,5}, of cardinality 4, while sunBound 3 2 is 5; the "
                    + "claimed inequality would be 5 ≤ 4, a contradiction.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sun-2021-conjecture-4-9-weighted-distinct-sums"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("sun-" + id), DeclarationHandle.Create(Prefix + Declaration(id)), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static string Declaration(string id) => id switch
    {
        "pf" => "pF",
        "weighted" => "weightedDistinctSums",
        "bound" => "sunBound",
        "claim" => "claim",
        "result" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        Apply(Named(name), args);
    private static Formula Apply(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ENat() => Call("WithTop", Nat());
    private static Formula FieldType(Formula f) => Call("Field", f);
    private static Formula Finset(Formula f) => Call("Finset", f);
    private static Formula IfThenElse(Formula condition, Formula then, Formula otherwise) =>
        Seq(F.Text, Grp(F.Id("if")), Sp, condition, Sp, F.Text, Grp(F.Id("then")), Sp, then,
            Sp, F.Text, Grp(F.Id("else")), Sp, otherwise);

    private static Formula PFormula()
    {
        var f = F.Id("F");
        var body = Eq(Call("pF", f), IfThenElse(Eq(Call("ringChar", f), D(0)),
            Call("top"), Cast(Call("ringChar", f), ENat())));
        return All("F", F.Id("Type"), Inst(FieldType(f), body));
    }

    private static Formula WeightedFormula()
    {
        var f = F.Id("F");
        var a = F.Id("A");
        var n = F.Id("n");
        var k = F.Id("k");
        var embedding = Apply(Qualified("Function", "Embedding"), Call("Fin", n), a);
        var summand = Mul(Cast(Add(Call("val", k), D(1)), f), Cast(Call("a", k), f));
        var sum = Seq(new Formula.Subscript(Sum, Seq(k, Sp, Colon, Sp, Call("Fin", n))), Sp, summand);
        var lambda = Seq(F.Text, Grp(F.Id("fun")), Sp, F.Id("a"), Sp, Mapsto, Sp, sum);
        var image = Apply(Qualified("Finset", "image"), lambda,
            Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Finset(embedding))));
        return All("F", F.Id("Type"), Inst(FieldType(f), Inst(Call("DecidableEq", f),
            All("A", Finset(f), All("n", Nat(), Eq(Call("weightedDistinctSums", a, n), image))))));
    }

    private static Formula BoundFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var div2 = Apply(Qualified("Nat", "div"), Mul(n, Add(n, D(1))), D(2));
        var div6 = Apply(Qualified("Nat", "div"), Mul(n, Sub(Pow(n, D(2)), D(1))), D(6));
        var body = Add(Add(Mul(Sub(m, n), div2), div6), D(1));
        return All("m", Nat(), All("n", Nat(), Eq(Call("sunBound", m, n), body)));
    }

    private static Formula ClaimFormula()
    {
        var f = F.Id("F");
        var n = F.Id("n");
        var a = F.Id("A");
        var body = Le(Call("min", Call("pF", f), Cast(Call("sunBound", Apply(Qualified("Finset", "card"), a), n), ENat())),
            Cast(Apply(Qualified("Finset", "card"), Call("weightedDistinctSums", a, n)), ENat()));
        body = All("A", Finset(f), body);
        body = Le(Add(n, Parenthesized(IfThenElse(Eq(n, D(3)), D(1), D(0)))), Apply(Qualified("Finset", "card"), a));
        body = All("A", Finset(f),
            new Formula.Logic(body, FormulaLogicOperator.Implies,
                Parenthesized(Le(Call("min", Call("pF", f), Cast(Call("sunBound", Apply(Qualified("Finset", "card"), a), n), ENat())),
                    Cast(Apply(Qualified("Finset", "card"), Call("weightedDistinctSums", a, n)), ENat())))));
        body = new Formula.Logic(Lt(Add(Cast(n, ENat()), D(1)), Call("pF", f)),
            FormulaLogicOperator.Implies, Parenthesized(body));
        body = new Formula.Logic(Le(D(1), n), FormulaLogicOperator.Implies, Parenthesized(body));
        body = All("n", Nat(), body);
        return All("F", F.Id("Type"), Inst(FieldType(f), Inst(Call("DecidableEq", f), body)));
    }

    private static Formula ResultFormula() => Disp(Seq(Neg, Sp, Call("claim")));
}
