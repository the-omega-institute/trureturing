using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class EvolutionAutomorphismTangentBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismTangentBridge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Q(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula InSet(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Fn(string name, Formula body) => Parenthesized(Seq(Name("fun"), Sp, X(name), Sp, Mapsto, Sp, body));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Field(Formula body) => All("k", Name("Type"), Instance(Call("Field", X("k")), body));
    private static Formula Vector(Formula k, Formula body) => All("V", Name("Type"),
        Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", k, X("V")), body)));
    private static Formula Ring(string r, Formula k, Formula body) => All(r, Name("Type"),
        Instance(Call("CommRing", X(r)), Instance(Call("Algebra", k, X(r)), body)));
    private static Formula LMap(Formula k, Formula a, Formula b) => Call("LinearMap", App(Q("RingHom", "id"), k), a, b);
    private static Formula Product(Formula k) => LMap(k, X("V"), LMap(k, X("V"), X("V")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Coordinates(Formula d) => Call("Sum", Call("Prod", Fin(d), Fin(d)), Name("Unit"));
    private static Formula GL(Formula d, Formula r) => App(Q("Matrix", "GeneralLinearGroup"), Fin(d), r);
    private static Formula Tensor(Formula k, Formula r) => Call("TensorProduct", k, r, X("V"));
    private static Formula Points(Formula r) => App(QualifiedValue(X("G"), "points"), r);
    private static Formula AutPoints(Formula r) => Call("automorphisms",
        App(Seq(Name("LinearMap"), Dot, Name("BilinMap"), Dot, Name("baseChange")), r, X("mu")));
    private static Formula CoeffMap(Formula f) => App(Q("TensorProduct", "map"),
        QualifiedValue(f, "toLinearMap"), Q("LinearMap", "id"));
    private static Formula QualifiedValue(Formula f, string name) => Seq(f, Dot, Name(name));
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula Polynomial(Formula d) => Call("MvPolynomial", Coordinates(d), X("k"));
    private static Formula SourceMatrix() => Call("Matrix", Fin(X("degree")), Fin(X("degree")), X("R"));
    private static DocumentBlock.Describe Desc(string name, Formula formula, string text,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create()
    {
        var k = X("k"); var v = X("V"); var mu = X("mu"); var r = X("R"); var s = X("S");
        var g = X("g"); var f = X("f"); var d = X("degree");
        var preservation = All("x", v, All("y", v,
            Eq(App(g, App(mu, X("x"), X("y"))), App(mu, App(g, X("x")), App(g, X("y"))))));
        var automorphismBody = Seq(OpenBrace, g, Colon, Call("LinearEquiv", App(Q("RingHom", "id"), r), v, v), Sp, Mid, Sp,
            preservation, CloseBrace);
        var automorphisms = All("R", Name("Type"), Instance(Call("CommRing", r), Vector(r,
            All("mu", Product(r), Eq(Call("automorphisms", mu), automorphismBody)))));
        var coords = Call("glCoordinates", g);
        var coordinateBody = And(
            All("i", Fin(d), All("j", Fin(d), Eq(App(coords, App(Q("Sum", "inl"), Pair(X("i"), X("j")))),
                App(Parenthesized(Seq(g, Sp, Colon, SourceMatrix())), X("i"), X("j"))))),
            All("u", Name("Unit"), Eq(App(coords, App(Q("Sum", "inr"), X("u"))),
                Val(App(Q("Inv", "inv"), App(Seq(Name("Matrix"), Dot, Name("GeneralLinearGroup"), Dot, Name("det")), g))))));
        var glCoordinates = All("degree", Name("Nat"), All("R", Name("Type"),
            Instance(Call("CommRing", r), All("g", GL(d, r), coordinateBody))));
        var pointType = Ring("R", k, Call("Subgroup", GL(d, r)));
        var pointValue = App(X("points"), r);
        var zeroLocus = Ring("R", k, All("g", GL(d, r), Iff(InSet(g, pointValue),
            All("p", Polynomial(d), Imp(InSet(X("p"), X("equations")),
                Eq(App(Seq(Name("MvPolynomial"), Dot, new Formula.Subscript(Name("eval"), D(2))), Call("algebraMap", k, r),
                    Call("glCoordinates", g), X("p")), D(0)))))));
        var mapped = App(Seq(Name("Matrix"), Dot, Name("GeneralLinearGroup"), Dot, Name("map")),
            QualifiedValue(f, "toRingHom"), g);
        var mapMem = Ring("R", k, Ring("S", k, All("f", Call("AlgHom", k, r, s),
            All("g", GL(d, r), Imp(InSet(g, pointValue), InSet(mapped, App(X("points"), s)))))));
        var group = Field(Eq(Call("LinearAlgebraicGroup", k), Seq(OpenBrace,
            d, Colon, Name("Nat"), Comma, Sp,
            X("equations"), Colon, Call("Set", Polynomial(d)), Comma, Sp,
            X("points"), Colon, pointType, Sp, Mid, Sp,
            And(Parenthesized(zeroLocus), Parenthesized(mapMem)), CloseBrace)));
        var equivType = Ring("R", k, Call("MulEquiv", Points(r), AutPoints(r)));
        var equivAt = App(X("equiv"), r, g);
        var mappedPoint = Seq(Langle, App(Seq(Name("Matrix"), Dot, Name("GeneralLinearGroup"), Dot, Name("map")),
            QualifiedValue(f, "toRingHom"), Val(g)), Comma, Sp,
            App(QualifiedValue(X("G"), "mapMem"), r, s, f, Val(g), QualifiedValue(g, "property")), Rangle);
        var naturality = Ring("R", k, Ring("S", k, All("f", Call("AlgHom", k, r, s),
            All("g", Points(r), All("x", Tensor(k, r),
                Eq(App(CoeffMap(f), App(Val(equivAt), X("x"))),
                    App(Val(App(X("equiv"), s, mappedPoint)), App(CoeffMap(f), X("x")))))))));
        var realizes = Field(Vector(k, All("G", Call("LinearAlgebraicGroup", k), All("mu", Product(k),
            Eq(Call("Realizes", X("G"), mu), Seq(OpenBrace, X("equiv"), Colon, equivType,
                Sp, Mid, Sp, naturality, CloseBrace))))));
        var polyMatrix = Fn("i", Fn("j", App(Q("MvPolynomial", "X"), App(Q("Sum", "inl"), Pair(X("i"), X("j"))))));
        var slEquation = new Formula.Binary(App(Q("Matrix", "det"), polyMatrix), FormulaBinaryOperator.Subtract, D(1));
        var slPoints = Seq(Name("fun"), Sp, Parenthesized(Seq(r, Colon, Name("Type"))), Sp,
            OpenBracket, Call("CommRing", r), CloseBracket, Sp,
            OpenBracket, Call("Algebra", Name("Complex"), r), CloseBracket, Sp, Mapsto, Sp, App(Q("MonoidHom", "ker"),
            Seq(Seq(Name("Matrix"), Dot, Name("GeneralLinearGroup"), Dot, Name("det")), Sp, Colon,
                Call("MonoidHom", GL(X("n"), r), Call("Units", r)))));
        var sl = All("n", Name("Nat"), Eq(Call("slGroup", X("n")), Seq(OpenBrace,
            Name("degree"), Colon, F.Eq, X("n"), Comma, Sp,
            Name("equations"), Colon, F.Eq, Seq(OpenBrace, slEquation, CloseBrace), Comma, Sp,
            Name("points"), Colon, F.Eq, slPoints, CloseBrace)));
        var tangent = Vector(Name("Complex"), All("mu", Product(Name("Complex")),
            Arrow(Call("Realizes", Call("slGroup", D(3)), mu),
                Call("Nonempty", Call("LieEquiv", Name("Complex"),
                    App(Seq(Name("LieAlgebra"), Dot, Name("SpecialLinear"), Dot, Name("sl")), Fin(D(3)), Name("Complex")),
                    Call("derivations", mu))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A natural SL3 realization identifies all infinitesimal automorphisms with derivations.",
            H("Evolution automorphisms and the tangent Lie algebra"), Blocks(
                Desc("automorphisms", automorphisms,
                    "All invertible linear maps preserving the given bilinear multiplication form a subgroup. No identity element or associativity of the multiplication is required.", AssessedProvenance.FromLiterature(Source)),
                Desc("glCoordinates", glCoordinates,
                    "The affine coordinates of GL consist of every matrix entry and the inverse determinant. The sum type adds one coordinate indexed by Unit.", AssessedProvenance.FromRepo(Source)),
                Desc("LinearAlgebraicGroup", group,
                    "A closed matrix group consists of a degree, polynomial equations and subgroups over every commutative coefficient algebra. Membership is exactly their common zero locus, and matrix maps preserve membership. The two conditions after the vertical bar are the zero-locus and change-of-algebra fields.", AssessedProvenance.FromRepo(Source)),
                Desc("Realizes", realizes,
                    "A realization consists of group equivalences over every commutative coefficient algebra, commuting with every algebra homomorphism on every tensor. TensorProduct.map uses the identity on V. This expresses an isomorphism of the full group-valued functors, including algebras with nilpotents.", AssessedProvenance.FromRepo(Source)),
                Desc("slGroup", sl,
                    "The single equation det(X) − 1 defines SL at every coefficient algebra. Its points are the kernel of the determinant homomorphism on Matrix.GeneralLinearGroup. The remaining structure fields prove the zero-locus characterization and preservation under matrix maps.", AssessedProvenance.FromLiterature(Source)),
                Desc("tangent_lie_equivalence", tangent,
                    "Dual-number coefficients reconstruct every derivation from a tangent automorphism. Addition is composition, scalar multiplication is substitution of epsilon, and the commutator over iterated dual numbers recovers the Lie bracket. Naturality therefore gives a complex Lie equivalence from trace-zero 3 by 3 matrices to all derivations.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));
    }
}
