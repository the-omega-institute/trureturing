using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Optimization;

internal sealed class WeightedCrownMomentCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/takahashietal2023su2sdp");
    private static readonly Formula N = F.Id("n"), X = F.Id("x"), M = F.Id("M");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Index() => Call("Option", Call("Option", Call("Fin", N)));
    private static Formula Mat(Formula index, Formula field) => Call("Matrix", index, index, field);
    private static Formula PairType() => Seq(OpenBrace, F.Id("s"), Colon, Call("Finset", Index()), Mid, Eq(Call("card", F.Id("s")), D(2)), CloseBrace);
    private static Formula MomentType() => Mat(Call("Option", PairType()), Real());
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, t));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(name, Colon, type)), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(name, Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula SumOver(Formula v, Formula t, Formula body) => Seq(new Formula.Subscript(Sum, Seq(v, Colon, t)), Parenthesized(body));
    private static Formula If(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula OverN(Formula f) => All(N, Nat(), f);
    private static Formula OverNX(Formula f) => OverN(All(X, Real(), f));
    private static Formula Region(Formula f) => OverN(Imp(Le(D(3), N), All(X, Real(), Imp(Lt(Call("L", N), X), Imp(Lt(X, Call("U", N)), f)))));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("weighted-crown-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A feasible level-one moment certificate with a strict value gap.",
        H("Weighted crown moment certificate"), Blocks(
            Node("L", "Crown interval boundary L", OverN(Eq(Call("L",N),Div(Pow(Add(Cast(N,Real()),D(2)),D(2)),Mul(D(4),Add(Cast(N,Real()),D(1)))))),
                "The lower boundary in Appendix C.1 is (n+2)^2/(4(n+1)).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("U", "Crown interval boundary U", OverN(Eq(Call("U",N),Div(Add(Cast(N,Real()),D(2)),D(3)))),
                "The upper boundary of the interval left open in Appendix C.1 is (n+2)/3.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("crownWeight", "The crown edge weights", OverNX(All(F.Id("e"),PairType(),Eq(Call("crownWeight",N,X,F.Id("e")),If(And(new Formula.Relation(Call("a",N),FormulaRelationOperator.MemberOf,Call("val",F.Id("e"))),new Formula.Relation(Call("b",N),FormulaRelationOperator.MemberOf,Call("val",F.Id("e")))),X,If(Or(new Formula.Relation(Call("a",N),FormulaRelationOperator.MemberOf,Call("val",F.Id("e"))),new Formula.Relation(Call("b",N),FormulaRelationOperator.MemberOf,Call("val",F.Id("e")))),D(1),D(0)))))),
                "The central edge has weight x, each spoke has weight 1, and every pair of leaves has weight 0.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("npa1Feasible", "Real level-one projector moments", OverN(All(M,MomentType(),Eq(Call("npa1Feasible",M),And(QCall("Matrix","IsSymm",M),And(QCall("Matrix","PosSemidef",M),And(Eq(App(M,F.Id("none"),F.Id("none")),D(1)),And(All(F.Id("e"),PairType(),Eq(App(M,Call("some",F.Id("e")),Call("some",F.Id("e"))),App(M,F.Id("none"),Call("some",F.Id("e"))))),All(F.Id("e"),PairType(),All(F.Id("f"),PairType(),All(F.Id("g"),PairType(),Imp(Eq(Call("card",QCall("Finset","inter",Call("val",F.Id("e")),Call("val",F.Id("f")))),D(1)),Imp(Eq(Call("val",F.Id("g")),Call("symmDiff",Call("val",F.Id("e")),Call("val",F.Id("f")))),Eq(Add(App(M,Call("some",F.Id("e")),Call("some",F.Id("f"))),App(M,Call("some",F.Id("f")),Call("some",F.Id("e")))),Div(Sub(Add(App(M,F.Id("none"),Call("some",F.Id("e"))),App(M,F.Id("none"),Call("some",F.Id("f")))),App(M,F.Id("none"),Call("some",F.Id("g")))),D(2))))))))))))))),
                "Section III defines NPA_l by positive semidefinite Hermitian moment matrices, identity normalization and the truncated operator relations. At the real first level these are exactly symmetry, the idempotent diagonals and the displayed adjacent-pair anticommutator. Disjoint commutation follows from symmetry.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("objective", "The moment objective", OverNX(All(M,MomentType(),Eq(Call("objective",X,M),SumOver(F.Id("e"),PairType(),Mul(Call("crownWeight",N,X,F.Id("e")),App(M,F.Id("none"),Call("some",F.Id("e")))))))),
                "The objective sums each unordered pair once, with the literal crown weights.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("npa1Value", "The real first-level optimum", OverNX(Eq(Call("npa1Value",N,X),Call("sSup",Seq(OpenBrace,F.Id("r"),Colon,Real(),Mid,Some(M,MomentType(),And(Call("npa1Feasible",M),Eq(F.Id("r"),Call("objective",X,M)))),CloseBrace)))),
                "The source proves NPA_1 = NPA_1^R for any weighted graph. The encoding takes the real supremum of exactly the feasible objective values.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("constructed_value_gap", "A strict moment-value gap", Region(Lt(Add(Cast(N,Real()),D(1)),Call("npa1Value",N,X))),
                "An explicit Gram matrix supplies a feasible moment matrix throughout L < x < U. Its objective is n+1+(x-L)^2/(32n), which is strictly above n+1. Positive rank-one summands and positive scalar block coefficients certify the matrix.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
}
