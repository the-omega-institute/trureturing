using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CommutatorGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/CommutatorGap.";
    public DocumentDefinition Create()
    {

        Formula n=F.Id("n"), m=F.Id("m"), a=F.Id("A"), b=F.Id("B"), c=F.Id("c"), u=F.Id("U"), v=F.Id("v"), ij=F.Id("ij"), i=F.Id("i"), j=F.Id("j"), w=F.Id("w");
        Formula np=Add(n,Num(1)),vh=Call("EuclideanSpace",C,Seq(Fin(n),Times,Fin(n)));
        Formula fs=Frob(a),gg=Call("gap",a),cc=Apply(Qualified("Complex","normSq"),c);
        Formula aa=Sub(a,Smul(c,Num(1)));
        Formula op=CLM(a),commOp=Call("commOperator",a);
        Formula scalarTranslation=LeqF(Call("opSq",aa),Add(Add(fs,Mul(Num(2),cc)),Mul(Mul(Num(2),Norm(c)),Apply(Qualified("Real","sqrt"),gg))));
        Formula co=Call("comparisonMatrix",a,c);
        Formula sub=Apply(Qualified("Matrix","submatrix"),a,Qualified("Fin","succ"),Qualified("Fin","succ"));
        Formula genericRect=Call("Matrix",Fin(m),Fin(n),C);
        return DocumentDefinition.Create(ScribeNode.Create("The commutator gap controls all scalar translations through a common block frame.",H("Commutator gap and scalar translation"),Blocks(
            Item("commOperator","Commutator operator in Hilbert coordinates",All([B("n",N),B("A",Mat(n))],Eqn(commOp,
                Call("toContinuousLinearMap",Call("comp",Call("toLinearMap",Call("vectorize",n)),Call("comp",Sub(Apply(Qualified("LinearMap","mulLeft"),C,a),Apply(Qualified("LinearMap","mulRight"),C,a)),Call("toLinearMap",Call("symm",Call("vectorize",n)))))))),
                "Conjugate the linear commutator map by vectorize and equip the finite-dimensional map with its continuous structure.",true),
            Item("gap","The commutator norm gap",All([B("n",N),B("A",Mat(n))],Eqn(gg,Sub(Mul(Num(2),fs),Pow(Norm(commOp),2)))),"The gap compares twice the Frobenius square with the squared operator norm of the commutator action.",true),
            Item("opSq","Squared matrix operator norm",All([B("n",N),B("A",Mat(n))],Eqn(Call("opSq",a),Pow(Norm(op),2))),"The matrix acts on the actual complex Euclidean space.",true),
            Item("comparisonMatrix","Real block comparison matrix",All([B("n",N),B("A",Mat(np)),B("c",C)],Eqn(co,
                Seq(OpenBracket,Parenthesized(Seq(Add(Norm(Apply(a,Num(0),Num(0))),Norm(c)),Comma,FrobeniusNorm(Apply(Qualified("Matrix","submatrix"),a,Seq(F.Id("i"),Mapsto,Num(0)),Qualified("Fin","succ"))))),F.Semi,
                    Parenthesized(Seq(Norm(Apply(Qualified("WithLp","toLp"),Num(2),Apply(Qualified("Function","comp"),Apply(Qualified("Matrix","col"),a,Num(0)),Qualified("Fin","succ")))),Comma,Add(FrobeniusNorm(sub),Norm(c)))),CloseBracket))),
                "These four nonnegative entries bound the norms of the two output blocks jointly. The subscript F denotes Mathlib's rectangular Frobenius norm.",true),
            Item("blockNorm_domination","Joint block domination",All([B("n",N),B("A",Mat(np)),B("c",C)],LeqF(Norm(CLM(aa)),Norm(CLM(co)))),"The real comparison operator acts on the pair consisting of the head modulus and tail norm of the same input vector."),
            Item("frobSq_unitary_right","Right unitary invariance",All([B("n",N),B("A",Mat(n)),B("U",Unit(n))],Eqn(Frob(Mul(a,Call("val",u))),fs)),"Trace cycling cancels the unitary and its conjugateTranspose."),
            Item("opSq_le_frobSq","Operator square is at most Frobenius square",All([B("n",N),B("A",Mat(n))],LeqF(Call("opSq",a),fs)),"The Frobenius multiplication inequality bounds every Euclidean input."),
            Item("gap_nonnegative","Nonnegative commutator gap",All([B("n",N),B("A",Mat(n))],LeqF(Num(0),gg)),"A maximizing pure vector provides a unitary block frame and a nonnegative lower bound. The empty dimension is included."),
            Item("translation_gap","Uniform scalar translation bound",All([B("n",N),B("A",Mat(n)),B("c",C)],scalarTranslation),"A maximizing block frame controls the real comparison matrix by its two-by-two Frobenius norm. Unitary covariance transfers the estimate to A."))));
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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, int p) => new Formula.Power(Parenthesized(a), Num(p));
    private static Formula FrobeniusNorm(Formula x) => Seq(Norm(x), Underscore, Grp(F.Id("F")));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Frob(Formula x) => Apply(Qualified("RHLinalg", "frobSq"), x);
    private static Formula Smul(Formula c, Formula x) => Seq(c, Cdot, Parenthesized(x));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), C);
    private static Formula All(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll, [..vs], b);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula CLM(Formula a) => Apply(Qualified("LinearMap", "toContinuousLinearMap"), Apply(Qualified("Matrix", "toEuclideanLin"), a));
    private static Formula Unit(Formula n) => Apply(Qualified("Matrix", "unitaryGroup"), Fin(n), C);
    private static DocumentBlock Item(string name, string title, Formula formula, string explanation,
        bool definition = false, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
