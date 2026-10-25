using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class NilpotencySpectrumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.";
    private static readonly LibraryNoteRef Survey = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private static Formula X(string x) => F.Id(x);
    private static Formula N(string x) => Seq(Operatorname, Grp(X(x)));
    private static Formula C(string x, params Formula[] args) => new Formula.Apply(N(x), [..args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [..args]);
    private static Formula All(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Some(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Inst(Formula t, Formula body) => Seq(OpenBracket, t, CloseBracket, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Rat => Seq(Mathbb, Grp(X("Q")));
    private static Formula Type => N("Type");
    private static Formula K => X("K");
    private static Formula V => X("V");
    private static Formula Mu => X("mu");
    private static Formula Bilinear => C("LinearMap", K, V, C("LinearMap", K, V, V));
    private static Formula Module => C("Submodule", K, V);
    private static Formula Bottom => Seq(Bot);
    private static Formula Top => Seq(TopToken);
    private static Formula Powers(Formula degree) => C("ordinaryPower", Mu, degree);
    private static Formula Context(Formula b) => All("K", Type, Inst(C("Field", K), All("V", Type,
        Inst(C("AddCommGroup", V), Inst(C("Module", K, V), All("mu", Bilinear, b))))));
    private static Formula BinaryCount => C("count", C("digits", D(2), X("k")), D(1));
    private static Formula Predicted => Or(Some("a", Nat, And(Eq(X("k"), Sup(D(2), X("a"))),
        Le(C("Int", X("a")), Sub(C("Int", X("n")), D(1))))),
        And(Le(D(2), BinaryCount), Le(Add(C("Int", C("log", D(2), X("k"))), C("Int", BinaryCount)), Sub(C("Int", X("n")), D(1)))));
    private static Formula ExistsBody => Some("V", Type, Some("g", C("AddCommGroup", V),
        Some("m", C("Module", K, V), Some("f", C("FiniteDimensional", K, V), Some("mu", Bilinear,
        And(Eq(C("finrank", K, V), X("n")), And(C("IsEvolutionAlgebra", Mu),
            And(Eq(Powers(Add(X("k"), D(1))), Bottom), Ne(Powers(X("k")), Bottom)))))))));
    private static Formula WholeClaim => All("K", Type, Inst(C("Field", K), Inst(C("Infinite", K),
        All("n", Nat, All("k", Nat, Imp(Le(D(1), X("k")), Iff(C("indexExists", K, X("n"), X("k")), C("predicted", X("n"), X("k")))))))));
    private static DocumentBlock.Describe Desc(string name, Formula formula, string text, DescribeRole role = DescribeRole.Definition, bool source = false) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), source ? AssessedProvenance.FromLiterature(Survey) : AssessedProvenance.FromRepo(Survey),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordinary nilpotency index outside the proposed binary spectrum.",
        H("An ordinary nilpotency index outside the proposed binary spectrum"), Blocks(
            Desc("productSpace", Context(All("U", Module, All("W", Module,
                Eq(C("productSpace", Mu, X("U"), X("W")), C("span", K,
                    Seq(OpenBrace, X("z"), Sp, Mid, Sp, Some("x", V, And(C("mem", X("x"), X("U")),
                        Some("y", V, And(C("mem", X("y"), X("W")), Eq(App(Mu, X("x"), X("y")), X("z")))))), CloseBrace)))))),
                "The product of two subspaces is the linear span of all products of their elements. Multiplication is bilinear; associativity is not assumed."),
            Desc("ordinaryPower", Context(And(Eq(Powers(D(0)), Bottom), And(Eq(Powers(D(1)), Top),
                All("n", Nat, Eq(Powers(Add(X("n"), D(2))), C("iSup", C("Fin", Add(X("n"), D(1))),
                    C("productSpace", Mu, Powers(Add(X("i"), D(1))), Powers(Sub(Add(X("n"), D(1)), X("i")))))))))),
                "For degree n+2 the supremum runs over i from 0 through n. Thus it contains every split into the positive degrees i+1 and n+1-i. This is the ordinary lower series in section 1.1, including every parenthesization. The zeroth power is unused for positive k.", source: true),
            Desc("indexExists", All("K", Type, Inst(C("Field", K), All("n", Nat, All("k", Nat,
                Eq(C("indexExists", K, X("n"), X("k")), ExistsBody))))),
                "The existential quantifiers range over the vector space, its additive group and scalar module structures, its finite-dimensionality, and the bilinear product. The natural-basis predicate is the existing evolution-algebra definition: commutativity and a basis with zero mixed products. Zero squares are permitted.", source: true),
            Desc("predicted", All("n", Nat, All("k", Nat, Eq(C("predicted", X("n"), X("k")), Predicted))),
                "The first branch is a power of two. In the second branch the number of digits equal to one in the base-two expansion is at least two. Natural logarithm here means the integer floor of the base-two logarithm. The dimension bound is the integer n minus one.", source: true),
            Desc("claim", Eq(N("claim"), WholeClaim),
                "Conjecture 9 of Kaygorodov, Martin Gonzalez and Viruel, arXiv:2610.22248v1, section 2.3, asserts this equivalence for every infinite field and every dimension, at each positive k. The nilpotency index in its wording is k+1.", source: true),
            Desc("product", All("x", Arrow(C("Fin", D(1,5)), Rat), All("y", Arrow(C("Fin", D(1,5)), Rat),
                Eq(C("product", X("x"), X("y")), C("sum", C("Fin", D(1,5)), C("smul", Mul(App(X("x"), X("i")), App(X("y"), X("i"))), App(X("r"), X("i"))))))),
                "In one-based coordinates the natural square rows r are: e2+e3+e5; -e4-e5; e4+e5; -e6-e8; e6+e8; e7+e8; -e9-e14; e9+e14; e10; e11; e12; e13+e14; -e15; e15; 0. The standard coordinate vectors form a natural basis. All mixed products vanish."),
            Desc("result", Seq(Neg, Sp, N("claim")),
                "Over the infinite field Q this fifteen-dimensional algebra has A^256=0 and A^255 nonzero. An integral triangular change of basis gives weights 1,2,1,3,1,5,10,1,15,30,60,120,240,1,255. Products increase weights additively, so every ordinary power A^m lies in the span of vectors of weight at least m. A product with 255 leaves equals e15: the successive degrees are 2,3,5,10,15,30,60,120,240,255. Hence the ordinary index is exactly 256. At k=255 there are eight one digits and floor(log2(k))=7; their sum 15 exceeds n-1=14, and k is not a power of two. Existence is true and both arithmetic alternatives are false.", DescribeRole.Theorem)
        )));
}
