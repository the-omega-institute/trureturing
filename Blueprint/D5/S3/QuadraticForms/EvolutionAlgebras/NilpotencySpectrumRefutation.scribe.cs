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
    private static Formula Integer => Seq(Mathbb, Grp(X("Z")));
    private static Formula Rat => Seq(Mathbb, Grp(X("Q")));
    private static Formula Type => N("Type");
    private static Formula K => X("K");
    private static Formula V => X("V");
    private static Formula Mu => X("mu");
    private static Formula Bilinear => C("LinearMap", K, V, C("LinearMap", K, V, V));
    private static Formula Module => C("Submodule", K, V);
    private static Formula Bottom => N("bot");
    private static Formula Top => N("top");
    private static Formula Powers(Formula degree) => C("ordinaryPower", Mu, degree);
    private static Formula Context(Formula b) => All("K", Type, Inst(C("Field", K), All("V", Type,
        Inst(C("AddCommGroup", V), Inst(C("Module", K, V), All("mu", Bilinear, b))))));
    private static Formula BinaryCount => C("count", C("digits", D(2), C("toNat", X("k"))), D(1));
    private static Formula Predicted => Or(Some("a", Nat, And(Eq(X("k"), new Formula.Power(D(2), X("a"))),
        Le(C("Int", X("a")), Sub(X("n"), D(1))))),
        And(Le(D(2), BinaryCount), Le(Add(C("Int", C("log", D(2), C("toNat", X("k")))), C("Int", BinaryCount)), Sub(X("n"), D(1)))));
    private static Formula Lam(string x, Formula t, Formula body) =>
        Seq(N("fun"), Sp, Open, X(x), Colon, t, Close, Sp, Mapsto, Sp, body);
    private static Formula SomeClass(Formula t, Formula body) =>
        Seq(Exists, Sp, OpenBracket, t, CloseBracket, Comma, Sp, body);
    private static Formula ExistsBody
    {
        get
        {
            var body = And(Eq(C("finrank", K, V), X("n")),
                And(C("IsEvolutionAlgebra", Mu),
                    And(Eq(Powers(Add(X("k"), D(1))), Bottom), Ne(Powers(X("k")), Bottom))));
            body = Some("mu", Bilinear, body);
            body = SomeClass(C("FiniteDimensional", K, V), body);
            body = SomeClass(C("Module", K, V), body);
            body = SomeClass(C("AddCommGroup", V), body);
            return Some("V", Type, body);
        }
    }
    private static Formula WholeClaim
    {
        get
        {
            var body = Iff(C("indexExists", K, C("toNat", X("n")), C("toNat", X("k"))), C("predicted", X("n"), X("k")));
            body = Imp(Le(D(0), X("n")), Imp(Le(D(1), X("k")), body));
            body = All("n", Integer, All("k", Integer, body));
            return All("K", Type, Inst(C("Field", K), Inst(C("Infinite", K), body)));
        }
    }
    private static Formula ProductSpaceFormula
    {
        get
        {
            var elements = Some("x", V, And(C("mem", X("x"), X("U")),
                Some("y", V, And(C("mem", X("y"), X("W")), Eq(App(Mu, X("x"), X("y")), X("z"))))));
            var set = Seq(OpenBrace, X("z"), Colon, V, Sp, Mid, Sp, elements, CloseBrace);
            return Context(All("U", Module, All("W", Module,
                Eq(C("productSpace", Mu, X("U"), X("W")), C("span", K, set)))));
        }
    }
    private static Formula PowerFormula
    {
        get
        {
            var degree = Add(X("n"), D(1));
            var summand = C("productSpace", Mu, Powers(Add(C("val", X("i")), D(1))),
                Powers(Sub(degree, C("val", X("i")))));
            var sum = C("iSup", Lam("i", C("Fin", degree), summand));
            var recurrence = All("n", Nat, Eq(Powers(Add(X("n"), D(2))), sum));
            return Context(And(Eq(Powers(D(0)), Bottom), And(Eq(Powers(D(1)), Top), recurrence)));
        }
    }
    private static Formula Diagonal(byte i) => Mul(App(X("x"), D(i)), App(X("y"), D(i)));
    private static Formula Diagonal(byte i, byte j) => Mul(App(X("x"), D(i,j)), App(X("y"), D(i,j)));
    private static Formula ProductFormula
    {
        get
        {
            var aa = Sub(Diagonal(2), Diagonal(1));
            var bb = Sub(Diagonal(4), Diagonal(3));
            var cc = Sub(Diagonal(7), Diagonal(6));
            var entries = new Formula[] {D(0), Diagonal(0), Diagonal(0), aa, Add(Diagonal(0), aa),
                bb, Diagonal(5), Add(bb, Diagonal(5)), cc, Diagonal(8), Diagonal(9),
                Diagonal(1,0), Diagonal(1,1), Add(cc, Diagonal(1,1)), Sub(Diagonal(1,3), Diagonal(1,2))};
            var vector = C("vector", entries);
            var space = Arrow(C("Fin", D(1,5)), Rat);
            return All("x", space, All("y", space, Eq(C("product", X("x"), X("y")), vector)));
        }
    }
    private static DocumentBlock.Describe Desc(string name, Formula formula, string text, DescribeRole role = DescribeRole.Definition, bool source = false,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name switch { "productSpace" => "product-space", "ordinaryPower" => "ordinary-power", "indexExists" => "index-exists", _ => name }), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), source ? AssessedProvenance.FromLiterature(Survey) : AssessedProvenance.FromRepo(Survey),
            Blocks(Paragraph(Text(text))), role, openProblemResolutionClaim: resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordinary nilpotency index outside the proposed binary spectrum.",
        H("An ordinary nilpotency index outside the proposed binary spectrum"), Blocks(
            Desc("productSpace", ProductSpaceFormula,
                "The product of two subspaces is the linear span of all products of their elements. Multiplication is bilinear; associativity is not assumed."),
            Desc("ordinaryPower", PowerFormula,
                "For degree n+2 the supremum runs over i from 0 through n. Thus it contains every split into the positive degrees i+1 and n+1-i. This is the ordinary lower series in section 1.1, including every parenthesization. The zeroth power is unused for positive k.", source: true),
            Desc("indexExists", All("K", Type, Inst(C("Field", K), All("n", Nat, All("k", Nat,
                Eq(C("indexExists", K, X("n"), X("k")), ExistsBody))))),
                "The existential quantifiers range over the vector space, its additive group and scalar module structures, its finite-dimensionality, and the bilinear product. The natural-basis predicate is the existing evolution-algebra definition: commutativity and a basis with zero mixed products. Zero squares are permitted.", source: true),
            Desc("predicted", All("n", Integer, All("k", Integer, Eq(C("predicted", X("n"), X("k")), Predicted))),
                "The first branch is a power of two. In the second branch the number of digits equal to one in the base-two expansion is at least two. The function log here means the integer floor of the base-two logarithm. The dimension bound is the integer n minus one. Int denotes the cast from natural numbers to integers; toNat converts the nonnegative integer argument to its natural-number representative.", source: true),
            Desc("claim", Eq(N("claim"), WholeClaim),
                "Conjecture 9 of Kaygorodov, Martin Gonzalez and Viruel, arXiv:2610.22248v1, section 2.3, asserts this equivalence for every infinite field and every nonnegative integer dimension n, at each positive integer k. The nilpotency index in its wording is k+1.", source: true),
            Desc("product", ProductFormula,
                "In one-based coordinates the natural square rows r are: e2+e3+e5; -e4-e5; e4+e5; -e6-e8; e6+e8; e7+e8; -e9-e14; e9+e14; e10; e11; e12; e13+e14; -e15; e15; 0. The displayed vector uses zero-based coordinate subscripts; the square-row description uses one-based subscripts. The standard coordinate vectors form a natural basis. All mixed products vanish."),
            Desc("result", Seq(Neg, Sp, N("claim")),
                "Over the infinite field Q this fifteen-dimensional algebra has A^256=0 and A^255 nonzero. The triangular spanning vectors, in order, are e1; e2+e3+e5; e3; e4+e5; e5; e6+e8; e7+e8+e9+e14; e8; e9+e14; e10+e15; e11; e12; e13+e14; e14; e15. Their weights are 1,2,1,3,1,5,10,1,15,30,60,120,240,1,255. Every nonzero product of two such vectors is another vector whose weight is at least the sum of the input weights. Bilinearity therefore gives F_r F_s contained in F_(r+s) for every positive r,s, where F_m spans vectors of weight at least m. Strong induction over all splits gives A^m contained in F_m; F_256 is zero. Starting from e1, and using e3 as the separate degree-one leaf at the second step, the input degree pairs are (1,1), (2,1), (3,2), (5,5), (10,5), (15,15), (30,30), (60,60), (120,120), (240,15). Their outputs are respectively the second, fourth, sixth, seventh, ninth, tenth, eleventh, twelfth, thirteenth and fifteenth spanning vectors. The final product has 255 leaves and equals e15. Hence the ordinary index is exactly 256. At k=255 there are eight one digits and floor(log2(k))=7; their sum 15 exceeds n-1=14, and k is not a power of two. Existence is true and both arithmetic alternatives are false.", DescribeRole.Theorem, resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kaygorodov-martin-gonzalez-viruel-2026-nilpotency-spectrum-conjecture-9"),
                    ResolutionKind.Refuted))
        )));
}
