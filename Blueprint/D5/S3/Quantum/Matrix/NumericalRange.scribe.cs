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
            Item("blochPure_norm","The unit-spinor Bloch image is on the sphere",
                All([B("v",Vec(Num(2)))],Imp(Eqn(Norm(v),Num(1)),
                    Eqn(Norm(PureBloch(v)),Num(1)))),
                "The outer product is Hermitian, has trace one and is idempotent. The existing Hermitian Bloch geometry gives its unit Euclidean norm."),
            Item("blochPure_surjective","Every Bloch sphere point has a unit spinor",
                All([B("r",RealVec(Num(3)))],Imp(Eqn(Norm(F.Id("r")),Num(1)),
                    Ex([B("v",Vec(Num(2)))],And(Eqn(Norm(v),Num(1)),Eqn(PureBloch(v),F.Id("r")))))),
                "This is the original all-poles square-root construction: the south pole has its own representative, and every other point uses the nonzero northern denominator."),
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
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2009variance"))),
            new DocumentBlock.Section(H("Application: the unit-spinor phase quotient"), Blocks(
                Paragraph(Text("Let U be the subset of EuclideanSpace C (Fin 2) defined by normSq(a)+normSq(b)=1, and let V be the subset of EuclideanSpace R (Fin 3) defined by q(0)^2+q(1)^2+q(2)^2=1. Both carry their inherited standard Euclidean topology. U is the Euclidean three-sphere; the unit sphere for the default maximum norm on C x C is a different subset. The finite WithLp coordinate homeomorphism identifies the coordinate descriptions without changing either subset topology.")),
                Paragraph(Text("On every representative (a,b), define H(a,b)=(2 Re(conj(a)b), 2 Im(conj(a)b), normSq(a)-normSq(b)). This is exactly bloch(vecMulVec v (star v)): the off-diagonal entry is a conj(b), and the minus sign in bloch's imaginary coordinate changes it to the displayed positive 2 Im(conj(a)b). The equality normSq(a)+normSq(b)=1 is equivalent to the Euclidean norm equation norm(v)=1, and the analogous sum-of-squares equation is equivalent to norm(q)=1. Therefore blochPure_norm places H in V, and blochPure_surjective supplies a representative for every point of V, including both poles.")),
                Paragraph(Text("Convert v in U to the existing Ket (Fin 2) with vec=v.ofLp and its same sum-of-squared-norms normalization proof. Pull back Ket.PhaseEquiv along this conversion. The resulting relation is precisely: v is equivalent to w if and only if there is one common c in C with normSq(c)=1 and v(i)=c w(i) for both coordinates i. No separate phase on each coordinate is allowed. Give the resulting Quotient its standard quotient topology.")),
                Paragraph(Text("MState.pure of that ket has matrix vecMulVec v (star v). The first component of bloch_geometry_of_isHermitian reconstructs this matrix as blochMatrix 1 (H(v)); its trace is one. Equal H values thus give equal pure matrices and equal MState values. Conversely equal pure states give equal H values. MState.PhaseEquiv_iff_pure_eq, equivalently MState.pure_eq_pure_iff, identifies these fibers with exactly the pulled-back common unit-complex phase relation. This uses the original normalized-ket fiber theorem rather than a new phase-extraction proof.")),
                Paragraph(Text("The quadratic map H is continuous by finite-coordinate polynomial continuity, complex conjugation and real/imaginary projection. Quotient.lift therefore induces a continuous map from U modulo the common phase to V. The exact fiber equivalence makes it injective, and the original all-poles Bloch supplier makes it surjective. Equiv.ofBijective supplies the inverse set map and both inverse laws. U is a compact Euclidean unit sphere, its quotient is compact, and V is Hausdorff. Pinned Mathlib Continuous.homeoOfEquivCompactToT2 upgrades this same map to a homeomorphism, proving inverse continuity without assuming it. Its value on every quotient representative remains the displayed H formula.")),
                Paragraph(Text("The normalized unit-spinor phase quotient homeomorphism is a consequence of these existing local suppliers and the standard compact-to-Hausdorff theorem. Its scope does not include the full nonzero scaled quotient, classification of phase-invariant polynomials, physical preparation or compression protocols, or absence of a continuous global section. Those stronger conclusions require separate arguments.")))))));
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
    private static Formula RealVec(Formula n) => Call("EuclideanSpace", R, Fin(n));
    private static Formula PureBloch(Formula v) =>
        Apply(Qualified("ActualPureQubitCostInfimum", "bloch"),
            Apply(Qualified("Matrix", "vecMulVec"),
                Apply(Qualified("WithLp", "ofLp"),v),
                Call("star",Apply(Qualified("WithLp", "ofLp"),v))));
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
