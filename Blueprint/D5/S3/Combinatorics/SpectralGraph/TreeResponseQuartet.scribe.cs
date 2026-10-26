using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class TreeResponseQuartetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.";

    public DocumentDefinition Create()
    {
        Formula v = V("V"), r = V("r"), m = V("M"), q = V("Q");
        Formula x = V("x"), y = V("y"), z = V("z");
        Formula b = V("B"), c = V("C"), g = V("G"), d = V("d");
        Formula a = V("a"), e = V("e"), p = V("P");
        Formula vertexB = V("b"), vertexC = V("c");
        Formula repeated = All("x", Real(), All("y", Real(), All("z", Real(),
            Eqn(Call("RepeatedMin", x, y, z), Or(And(Eqn(x, y), Le(y, z)),
                Or(And(Eqn(x, z), Le(z, y)), And(Eqn(y, z), Le(z, x))))))));
        Formula block = Data(All("M", MatrixV(), All("x", v, All("y", v,
            All("i", Fin(r), All("j", Fin(r),
                Eqn(App(Call("block", m, x, y), V("i"), V("j")),
                    App(m, Pair(x, V("i")), Pair(y, V("j"))))))))));
        Formula weight = Data(All("M", MatrixV(), All("x", v, All("y", v,
            Eqn(Call("weight", m, x, y), Abs(Det(Call("block", m, x, y))))))));
        Formula supported = Data(All("G", Call("SimpleGraph", v), All("M", MatrixV(),
            Eqn(Call("Supported", g, m), All("x", v, All("y", v,
                Imp(Ne(x, y), Imp(Neg(Call("Adj", g, x, y)),
                    Eqn(Call("block", m, x, y), D(0))))))))));
        Formula quartet = All("V", Type(), All("d", Fn(v, Fn(v, Real())),
            FourVertices(Eqn(Call("Quartet", d, a, vertexB, vertexC, e), QuartetBody(d, a, vertexB, vertexC, e)))));
        Formula cut = Data(All("Q", MatrixV(), All("B", Call("Set", v),
            All("C", Call("Set", v), All("x", Product(b, Fin(r)), All("y", Product(c, Fin(r)),
                Eqn(App(Call("cut", q, b, c), x, y),
                    App(q, Pair(Call("val", Call("fst", x)), Call("snd", x)),
                        Pair(Call("val", Call("fst", y)), Call("snd", y))))))))));
        Formula response = FiniteData(All("Q", MatrixV(), All("B", Call("Set", v),
            DecidableSet(b, Eqn(Call("response", q, b),
                Sub(Call("cut", q, b, b), Mul(Mul(Call("cut", q, b, Compl(b)),
                    Inv(Call("cut", q, Compl(b), Compl(b)))), Call("cut", q, Compl(b), b))))))));
        Formula inverse = FiniteData(All("G", Call("SimpleGraph", v), All("Q", MatrixV(),
            Imp(Call("IsTree", g), Imp(Call("IsHermitianPositiveDefinite", q),
                Imp(Call("Supported", g, q), FourVertices(
                    QuartetBody(Call("weight", Inv(q)), a, vertexB, vertexC, e))))))));
        Formula shifted = Sub(V("H"), Mul(z, D(1)));
        Formula sourceConclusion = QuartetBody(Call("weight", Call("response", shifted, b)),
            App(p, D(0)), App(p, D(1)), App(p, D(2)), App(p, D(3)));
        Formula retainedData = All("B", Call("Set", v), DecidableSet(b,
            Imp(Call("IsHermitianPositiveDefinite", Call("cut", shifted, Compl(b), Compl(b))),
                All("P", Embedding(Fin(D(4)), b), sourceConclusion))));
        Formula source = FiniteData(All("T", Call("SimpleGraph", v), All("H", MatrixV(),
            Imp(Call("IsTree", V("T")), Imp(Call("IsSymm", V("H")),
                Imp(Call("Supported", V("T"), V("H")), All("z", Real(), retainedData)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The full determinant quartet for a real tree response with only the eliminated block positive definite.",
            H("Full block determinant quartets on trees"), Blocks(
                Paragraph(Text("Every vertex has the same complete real fibre. Blocks are read in the original coordinate basis. Edge blocks may be singular or zero, and diagonal blocks are unrestricted except for the stated positivity of the eliminated principal block.")),
                Node("minimum", "A repeated minimum", "RepeatedMin", repeated,
                    "The three possible equalities include the case where all three values coincide.", DescribeRole.Definition),
                Node("block", "Complete vertex blocks", "block", block,
                    "The row and column maps keep all r coordinates of each named actual vertex.", DescribeRole.Definition),
                Node("weight", "Absolute full determinants", "weight", weight,
                    "This is the determinant of the entire r by r block, followed by absolute value. It is not an operator norm or a selected singular value.", DescribeRole.Definition),
                Node("support", "Tree support", "Supported", supported,
                    "Distinct nonadjacent vertices have zero blocks. The condition allows arbitrary diagonal blocks and arbitrary rank on every edge.", DescribeRole.Definition),
                Node("quartet", "Three pairings", "Quartet", quartet,
                    "The three products correspond to the perfect matchings ab|ce, ac|be, and ae|bc. This predicate also allows coincident marked vertices.", DescribeRole.Definition),
                Node("cut", "Original rectangular restrictions", "cut", cut,
                    "Restrictions select coordinates without recalculating any diagonal entry. The type B denotes the subtype of vertices belonging to B.", DescribeRole.Definition),
                Node("response", "Eliminating the complement", "response", response,
                    "Only the complement of B is eliminated. In the four selected response blocks, every extra retained vertex is grounded at zero. An empty complement gives a zero elimination term.", DescribeRole.Definition),
                Node("inverse", "The inverse-tree quartet", "inverse_tree_quartet", inverse,
                    "Delete a leaf v with neighbor u and take its positive-definite diagonal Schur complement. The remaining inverse is the principal inverse block. Every cross block from v factors through u with the actual leaf transport matrix. The leaf diagonal inverse is its positive conditional covariance plus the transported neighbor covariance. The existing Gram determinant comparison bounds the determinant of the transported part, including singular transport. Induction on the number of vertices proves the quartet. When a marked leaf is replaced by its neighbor, marked vertices may coincide; the repeated-vertex induction statement handles this case.", DescribeRole.Theorem),
                Node("responsequartet", "The actual-response quartet", "complete263_2", source,
                    "Write Q = H - z Id and S for its Schur response on B. Add a common positive diagonal m Id at all retained vertices. Internal positivity and a spectral bound for S make this auxiliary tree matrix positive definite for every sufficiently large m. Its inverse restricted to B is (S + m Id) inverse. The inverse-tree quartet therefore applies to all four actual ports, regardless of their degrees or positions. The matrix S (Id + S/m) inverse equals m Id - m squared times (S + m Id) inverse and converges to S. Its six off-diagonal blocks are common scalar multiples of the corresponding auxiliary inverse blocks. Full determinants preserve this common scaling, and the repeated-minimum condition is closed under limits. This proves the original response law with no global positivity. The embedding of Fin 4 into B supplies four distinct ordered actual ports and entails at least four vertices. The theorem permits every natural r, so in particular includes all required r at least one; the zero-dimensional extension imposes no restriction on the stated result. Neither the construction nor the limit changes the original basis or units.", DescribeRole.Theorem))));
    }

    private static DocumentBlock Node(string id, string title, string name, Formula f, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("tree-response-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? C(s) : App(C(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Neg(Formula a) => new Formula.Not(a);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Inv(Formula a) => new Formula.Power(a, new Formula.Negate(D(1)));
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Det(Formula a) => Call("det", a);
    private static Formula Compl(Formula a) => Call("compl", a);
    private static Formula Fin(Formula a) => Call("Fin", a);
    private static Formula Real() => C("Real");
    private static Formula Type() => C("Type");
    private static Formula Nat() => C("Nat");
    private static Formula MatrixV() => Call("Matrix", Product(V("V"), Fin(V("r"))), Product(V("V"), Fin(V("r"))), Real());
    private static Formula Embedding(Formula a, Formula b) => Call("Embedding", a, b);
    private static Formula Instance(string name, Formula body) =>
        Seq(OpenBracket, Call(name, V("V")), CloseBracket, Sp, body);
    private static Formula Data(Formula body) => All("V", Type(), All("r", Nat(), body));
    private static Formula FiniteData(Formula body) => All("V", Type(), Instance("Fintype", Instance("DecidableEq", All("r", Nat(), body))));
    private static Formula DecidableSet(Formula set, Formula body) =>
        Seq(OpenBracket, Call("DecidableMembership", set), CloseBracket, Sp, body);
    private static Formula FourVertices(Formula body) =>
        All("a", V("V"), All("b", V("V"), All("c", V("V"), All("e", V("V"), body))));
    private static Formula QuartetBody(Formula d, Formula a, Formula b, Formula c, Formula e) =>
        Call("RepeatedMin", Mul(App(d, a, b), App(d, c, e)), Mul(App(d, a, c), App(d, b, e)), Mul(App(d, a, e), App(d, b, c)));
}
