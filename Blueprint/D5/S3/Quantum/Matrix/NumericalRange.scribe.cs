using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class NumericalRangeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/NumericalRange.";
    public DocumentDefinition Create()
    {

        Formula e=F.Id("E"), f=F.Id("F"), l=F.Id("L"), k=F.Id("k"), a=F.Id("A"), v=F.Id("v"), z=F.Id("z"), n=F.Id("n"), bigK=F.Id("K");
        Formula range=SetOf("z",C,Ex([B("v",e)],And(Eqn(Norm(v),Num(1)),Eqn(z,Inner(v,Apply(a,v))))));
        Formula finiteInstances=Seq(Inst("NormedAddCommGroup",e),Inst("InnerProductSpace",C,e),Inst("FiniteDimensional",C,e));
        return DocumentDefinition.Create(ScribeNode.Create("Numerical ranges are convex under finite-dimensional compression.", H("Numerical ranges and compression"), Blocks(
            Item("sphere_image_eq_ball_image","An invisible direction reaches the sphere",
                All([B("E",F.Id("Type")), B("F",F.Id("Type"))], Seq(Inst("NormedAddCommGroup",e),Inst("NormedSpace",R,e),Inst("AddCommGroup",f),Inst("Module",R,f),
                    All([B("L",Lin(e,R,f)),B("k",e)],Imp(And(Ne(k,Num(0)),Eqn(Apply(l,k),Num(0))),
                        Eqn(Apply(Qualified("Set","image"),l,Apply(Qualified("Metric","sphere"),Num(0),Num(1))),
                            Apply(Qualified("Set","image"),l,Apply(Qualified("Metric","closedBall"),Num(0),Num(1)))))))),
                "A nonzero kernel direction carries every point in the closed unit ball to the unit sphere without changing its linear image."),
            Item("innerNumericalRange","Inner-product numerical range",
                All([B("E",F.Id("Type"))],Seq(Inst("NormedAddCommGroup",e),Inst("InnerProductSpace",C,e),
                    All([B("A",Lin(e,C,e,true))],Eqn(Call("innerNumericalRange",a),range)))),
                "The values are complex expectations on unit vectors. The inner product is conjugate-linear in its first argument.",true),
            Item("finite_numericalRange_convex","Toeplitz-Hausdorff in finite dimension",
                All([B("E",F.Id("Type"))],Seq(finiteInstances,All([B("A",Lin(e,C,e,true))],Call("Convex",R,Call("innerNumericalRange",a))))),
                "The span of two vectors has complex dimension at most two. Its compressed operator has a convex numerical range, and the inclusion preserves both expectations.",false,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2009variance"))),
            Item("subspaceNumericalRange","Expectations restricted to a subspace",
                All([B("n",N),B("A",Mat(n)),B("K",Call("Submodule",C,Vec(n)))],
                    Eqn(Call("subspaceNumericalRange",a,bigK),SetOf("z",C,Ex([B("v",bigK)],And(Eqn(Norm(v),Num(1)),
                        Eqn(z,Inner(Call("val",v),ToLin(a,Call("val",v))))))))),
                "The vector is in K and is coerced to the ambient Euclidean space for the expectation.",true),
            Item("subspace_numericalRange_convex","Every compressed numerical range is convex",
                All([B("n",N),B("A",Mat(n)),B("K",Call("Submodule",C,Vec(n)))],Call("Convex",R,Call("subspaceNumericalRange",a,bigK))),
                "An orthonormal basis identifies the subspace with a finite Euclidean space; compression preserves the complex expectation.",false,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2009variance"))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Apply(Formula f, params Formula[] args) =>
        Seq(f, Parenthesized(CommaList(args)));
    private static Formula CommaList(Formula[] values) => values.Length == 0 ? Seq(Sp) :
        Seq(values.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray());
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), C);
    private static Formula Vec(Formula n) => Call("EuclideanSpace", C, Fin(n));
    private static Formula Lin(Formula a, Formula scalar, Formula b, bool continuous = false) =>
        Seq(a, To, Underscore, Grp(F.Id(continuous ? "L" : "l")), OpenBracket, scalar, CloseBracket, b);
    private static Formula All(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll, [..vs], b);
    private static Formula Ex(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.Exists, [..vs], b);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Inst(string name, params Formula[] a) => Seq(OpenBracket, Call(name, a), CloseBracket, Sp);
    private static Formula Inner(Formula v, Formula w) => Call("inner", C, v, w);
    private static Formula ToLin(Formula a, Formula v) => Apply(Apply(Qualified("Matrix", "toEuclideanLin"), a), v);
    private static Formula SetOf(string z, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(z), Colon, type, Mid, body, CloseBrace);
    private static DocumentBlock Item(string name, string title, Formula formula, string explanation,
        bool definition = false, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
