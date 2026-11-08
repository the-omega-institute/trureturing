using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class CallanA002067DyckDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/callan2017a002067");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted Dyck-path sum satisfies the A002067 convolution, through a polynomial model for arbitrary up/down words.",
        H("Callan's weighted Dyck paths"),
        Blocks(
            Node("source-sequence", "The source sequence", "IsSourceSequence", SequenceFormula(),
                "OEIS A002067, NAME (unnumbered entry, no page number): \"a(n) = Sum_{k=0..n-1} binomial(2*n,2*k)*a(k)*a(n-k-1).\" The offset and source program set a(0)=1. The source index n >= 1 is written as n+1; k runs from 0 to n.",
                AssessedProvenance.FromLiterature(Source)),
            Node("prefix-height", "Prefix height", "prefixHeight", HeightFormula(),
                "The natural height is the number of U steps minus the number of D steps in the first j steps. Natural-number subtraction is truncated at zero; the Dyck prefix inequalities ensure that no truncation changes a path height.",
                AssessedProvenance.FromLiterature(Source)),
            Node("path-weight", "Weight of one path", "pathWeight", WeightFormula(),
                "OEIS A002067, Callan COMMENTS (unnumbered entry, no page number): \"a(n) is the total weight of Dyck n-paths with weight defined as follows. Given a Dyck path, for each upstep, record its position in the path and the height of its upper endpoint; then multiply together all of these positions and heights. For example, the Dyck 4-path P = UUDUUDDD has upsteps in positions 1,2,4,5 ending at heights 1,2,2,3 respectively, and hence weight(P) = 480. (In fact the positions determine the heights because, for the k-th upstep, position + height = 2k.)\" Positions are one-based; the index j in the formula is zero-based, so position and upper height are j+1 and prefixHeight(p,j+1).",
                AssessedProvenance.FromLiterature(Source)),
            Node("dyck-sum", "Total path weight", "weightedDyckSum", SumFormula(),
                "The sum ranges over every Mathlib DyckWord of semilength n. It includes the empty word at n = 0. The value of the product over its empty set of upsteps is one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("walk-polynomial", "Derivative polynomials", "walkPoly", WalkFormula(),
                "Dominici, arXiv:math/0607230v2, Section 3: P_{n+1}(x)=P'_{n}(x)+(n+1)xP_n(x), with P_0(x)=1. The coefficient ring here is the natural numbers. Polynomial differentiation counts the choices of a closing step; multiplication by (n+1)X adds an opening step at position n+1.",
                AssessedProvenance.FromLiterature(Source)),
            Node("sequence-unique", "Uniqueness of the recurrence", "source_unique", UniqueFormula(),
                "Strong induction identifies any two solutions: both indices k and n-k in the recurrence for n+1 are smaller than n+1.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("polynomial-source", "Returning coefficients solve the recurrence", "poly_is_source", PolyFormula(),
                "A derivative convolution follows from Pascal's identity by induction. Coefficients of the wrong parity vanish, so evaluation at zero in even degree gives exactly the source recurrence.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("dyck-identity", "The weighted Dyck identity", "source_eq_dyck", IdentityFormula(),
                "For every length, summing the polynomial contributions of all up/down words gives walkPoly. A word contributes zero if a prefix is negative; otherwise it contributes its step weight times X raised to its final height. Evaluation at zero selects returning paths. A factorial crossing invariant equates products of upstep upper heights and downstep starting heights.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("callan-" + id), DeclarationHandle.Create(LeanPrefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Range(Formula n) => Qualified("Finset", "range", n);
    private static Formula SumIn(Formula binder, Formula body) => Seq(new Formula.Subscript(Sum, binder), Sp, body);
    private static Formula ProdIn(Formula binder, Formula body) => Seq(new Formula.Subscript(Prod, binder), Sp, body);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));

    private static Formula Steps(Formula p) => Qualified("DyckWord", "toList", p);
    private static Formula Length(Formula w) => Qualified("List", "length", w);
    private static Formula Lookup(Formula w, Formula j) => Qualified("List", "getD", w, j,
        Seq(Operatorname, Grp(V("DyckStep"), Dot, V("D"))));
    private static Formula Up() => Seq(Operatorname, Grp(V("DyckStep"), Dot, V("U")));
    private static Formula IsUp(Formula p, Formula j) => Equal(Lookup(Steps(p), j), Up());
    private static Formula Prefix(Formula p, Formula j) => Qualified("List", "take", j, Steps(p));
    private static Formula HeightFormula()
    {
        var p = V("p"); var j = V("j");
        var prefix = Prefix(p, j);
        return All("p", Named("DyckWord"), All("j", N(), Equal(Call("prefixHeight", p, j),
            Sub(Qualified("List", "count", Up(), prefix),
                Qualified("List", "count", Seq(Operatorname, Grp(V("DyckStep"), Dot, V("D"))), prefix)))));
    }
    private static Formula SequenceFormula()
    {
        var a = V("a"); var n = V("n"); var k = V("k");
        var recurrence = All("n", N(), Equal(App(a, Add(n, D(1))),
            SumIn(Member(k, Range(Add(n, D(1)))),
                Mul(Mul(Qualified("Nat", "choose", Mul(D(2), Parenthesized(Add(n, D(1)))), Mul(D(2), k)),
                    App(a, k)), App(a, Sub(n, k))))));
        return All("a", Arrow(N(), N()), Equal(Call("IsSourceSequence", a),
            And(Equal(App(a, D(0)), D(1)), recurrence)));
    }
    private static Formula WeightFormula()
    {
        var p = V("p"); var j = V("j");
        var indices = Qualified("Finset", "filter", LambdaOf("j", N(), IsUp(p, j)), Range(Length(Steps(p))));
        return All("p", Named("DyckWord"), Equal(Call("pathWeight", p),
            ProdIn(Member(j, indices), Mul(Parenthesized(Add(j, D(1))), Call("prefixHeight", p, Add(j, D(1)))))));
    }
    private static Formula SumFormula()
    {
        var n = V("n"); var p = V("p");
        var domain = Seq(OpenBrace, p, Colon, Sp, Named("DyckWord"), Sp, Mid, Sp,
            Equal(Qualified("DyckWord", "semilength", p), n), CloseBrace);
        return All("n", N(), Equal(Call("weightedDyckSum", n),
            SumIn(Seq(p, Colon, Sp, domain), Call("pathWeight", Call("val", p)))));
    }
    private static Formula WalkFormula()
    {
        var n = V("n"); var p = Call("walkPoly", n);
        return new Formula.Aligned([
            Seq(Named("walkPoly"), Colon, Sp, Arrow(N(), Call("Polynomial", N()))),
            Equal(Call("walkPoly", D(0)), D(1)),
            All("n", N(), Equal(Call("walkPoly", Add(n, D(1))),
                Add(Qualified("Polynomial", "derivative", p),
                    Mul(Mul(Qualified("Polynomial", "C", Add(n, D(1))),
                        Seq(Operatorname, Grp(V("Polynomial"), Dot, V("X")))), p))))]);
    }
    private static Formula UniqueFormula()
    {
        var a = V("a"); var b = V("b");
        return All("a", Arrow(N(), N()), All("b", Arrow(N(), N()),
            Imp(Call("IsSourceSequence", a), Imp(Call("IsSourceSequence", b), Equal(a, b)))));
    }
    private static Formula PolyFormula() => Call("IsSourceSequence", LambdaOf("n", N(),
        Qualified("Polynomial", "eval", D(0), Call("walkPoly", Mul(D(2), V("n"))))));
    private static Formula IdentityFormula()
    {
        var a = V("a"); var n = V("n");
        return All("a", Arrow(N(), N()), Imp(Call("IsSourceSequence", a), All("n", N(),
            Equal(App(a, n), Call("weightedDyckSum", n)))));
    }
}
