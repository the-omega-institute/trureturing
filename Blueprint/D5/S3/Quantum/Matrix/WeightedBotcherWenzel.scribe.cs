using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class WeightedBotcherWenzelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/WeightedBotcherWenzel.";
    public DocumentDefinition Create()
    {

        Formula p=F.Id("P"),v=F.Id("V"),t=F.Id("t");
        Formula ws(Formula x, Formula y)=>Call("weightedSq",x,y);
        Formula n=F.Id("n"),w=F.Id("W"),a=F.Id("A"),b=F.Id("B"),lo=F.Id("lo"),hi=F.Id("hi"),h=F.Id("h"),i=F.Id("i");
        Formula eig=Apply(Call("eigenvalues",h),i);
        Formula spec=Ex([B("h",Apply(Qualified("Matrix","IsHermitian"),w))],And(All([B("i",Fin(n))],And(LeqF(lo,eig),LeqF(eig,hi))),
            And(Ex([B("i",Fin(n))],Eqn(eig,lo)),Ex([B("i",Fin(n))],Eqn(eig,hi)))));
        Formula assertion=All([B("n",N)],Imp(Lt(Num(0),n),All([B("W",Mat(n)),B("lo",R),B("hi",R)],
            Imp(Apply(Qualified("Matrix","PosDef"),w),Imp(Lt(Num(0),lo),Imp(Call("SpectralExtrema",w,lo,hi),All([B("A",Mat(n)),B("B",Mat(n))],
                LeqF(Call("weightedSq",Comm(a,b),w),Mul(Mul(Add(Num(1),Div(hi,lo)),Call("weightedSq",a,w)),Frob(b))))))))));
        return DocumentDefinition.Create(ScribeNode.Create("The squared weighted Bottcher-Wenzel conjecture holds for every positive definite weight.",H("Weighted Bottcher-Wenzel, case (ii)"),Blocks(
            Item("weightedSq","Squared weighted Frobenius norm",All([B("n",N),B("A",Mat(n)),B("W",Mat(n))],Eqn(ws(a,w),ReF(Trace(Mul(Mul(Adj(a),a),w))))),
                "The source defines: “In what follows we call ω-weighted Frobenius norm” followed by “‖A‖ω := √tr(A∗Aω)” (equation (2), page 2). This is its literal squared trace expression, using the real part for the real-valued result.",true,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/mayumi2024weightedbw"))),
            Item("weighted_add","Additive weight dependence",All([B("n",N),B("A",Mat(n)),B("W",Mat(n)),B("V",Mat(n))],Eqn(ws(a,Add(w,v)),Add(ws(a,w),ws(a,v)))),"Trace and right matrix multiplication are additive in the weight."),
            Item("weighted_smul","Real scaling of the weight",All([B("n",N),B("A",Mat(n)),B("W",Mat(n)),B("t",R)],Eqn(ws(a,Smul(t,w)),Mul(t,ws(a,w)))),"The real part of the trace respects real scalar multiplication."),
            Item("weighted_one","Identity weight",All([B("n",N),B("A",Mat(n))],Eqn(ws(a,Num(1)),Frob(a))),"The identity weight gives the ordinary Frobenius square."),
            Item("projected_trace","Projection weight equals projected norm",All([B("n",N),B("A",Mat(n)),B("P",Mat(n))],Imp(Projection(p),Eqn(ws(a,p),Frob(Mul(a,p))))),"Hermiticity and idempotence permit trace cycling to the Gram matrix of AP."),
            Item("projection_gap","Projection commutator channel bound",All([B("n",N),B("A",Mat(n)),B("B",Mat(n)),B("P",Mat(n))],Imp(Projection(p),
                LeqF(Frob(Mul(Comm(a,b),p)),Mul(Add(Add(Frob(a),Mul(Num(2),Frob(Mul(a,p)))),Mul(Num(2),Apply(Qualified("Real","sqrt"),Mul(Frob(Mul(a,p)),Call("gap",a))))),Frob(b))))),
                "The SVD expresses a contraction as an average of two actual unitaries. A common-radius bound for scalar pencils transfers to the projected adjoint channel, for every projection rank and including zero input matrices."),
            Item("SpectralExtrema","Attained spectral endpoints",All([B("n",N),B("W",Mat(n)),B("lo",R),B("hi",R)],IffF(Call("SpectralExtrema",w,lo,hi),spec)),"Every eigenvalue lies between lo and hi, and each endpoint is attained. Thus these parameters are exactly the smallest and largest eigenvalues, including repeated eigenvalues.",true),
            Item("result","The weighted inequality",F.Id("claim"),"The projection channel bound and nonnegative commutator gap give a square-completion lower bound for every two-level weight. A spectral convex decomposition transfers the inequality to an arbitrary positive definite weight. This statement is case (ii). Cases (i) and (iv) are separate questions.",false,
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/mayumi2024weightedbw"))))));
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
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Frob(Formula x) => Apply(Qualified("RHLinalg", "frobSq"), x);
    private static Formula Comm(Formula a, Formula b) => Call("commutator", a, b);
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), C);
    private static Formula All(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll, [..vs], b);
    private static Formula Ex(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.Exists, [..vs], b);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula ReF(Formula x) => Apply(Qualified("Complex", "re"), x);
    private static Formula Trace(Formula x) => Apply(Qualified("Matrix", "trace"), x);
    private static Formula Adj(Formula x) => Apply(Qualified("Matrix", "conjTranspose"), x);
    private static Formula Smul(Formula c, Formula x) => Seq(c, Cdot, Parenthesized(x));
    private static Formula Projection(Formula x) => And(Apply(Qualified("Matrix", "IsHermitian"), x), Eqn(Mul(x,x), x));
    private static DocumentBlock Item(string name, string title, Formula formula, string explanation,
        bool definition = false, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem, resolution);
}
