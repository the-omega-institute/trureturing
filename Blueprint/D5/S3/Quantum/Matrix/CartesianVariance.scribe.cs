using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CartesianVarianceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/CartesianVariance.";
    public DocumentDefinition Create()
    {

        Formula n=F.Id("n"), a=F.Id("A"), b=F.Id("B"), q=F.Id("Q"), rho=F.Id("rho"), v=F.Id("v"), i=F.Id("i"), j=F.Id("j"), sigma=F.Id("sigma");
        Formula cart=Smul(Div(Num(1),Num(2)),Add(Mul(Adj(a),a),Mul(a,Adj(a))));
        Formula var=Sub(ReF(Trace(Mul(rho,Parenthesized(cart)))),Apply(Qualified("Complex","normSq"),Trace(Mul(rho,a))));
        Formula pq=Pure(v);
        return DocumentDefinition.Create(ScribeNode.Create("A pure vector maximizes the Cartesian matrix variance.",H("Cartesian variance"),Blocks(
            Item("frobSq_eq_sum","Frobenius square in coordinates",All([B("n",N),B("A",Mat(n))],Eqn(Frob(a),Sum("i",Fin(n),Sum("j",Fin(n),Apply(Qualified("Complex","normSq"),Apply(a,j,i)))))),
                "The squared Frobenius norm is the sum of the squared moduli of all matrix entries."),
            Item("frobSq_nonneg","Nonnegative Frobenius square",All([B("n",N),B("A",Mat(n))],LeqF(Num(0),Frob(a))),"Every entry contributes a nonnegative square."),
            Item("vectorize","Matrix Hilbert-space coordinates",All([B("n",N)],Eqn(Call("vectorize",n),
                Apply(Qualified("LinearEquiv","trans"),
                    Apply(Qualified("LinearEquiv","symm"),Apply(Qualified("LinearEquiv","curry"),C,C,Fin(n),Fin(n))),
                    Apply(Qualified("LinearEquiv","symm"),Apply(Qualified("WithLp","linearEquiv"),Num(2),C,Arrow(Parenthesized(Seq(Fin(n),Times,Fin(n))),C)))))),
                "This complex linear equivalence arranges matrix entries by their ordered pair of indices. It composes Mathlib's inverse currying equivalence with the inverse WithLp linear equivalence.",true),
            Item("vectorize_norm_sq","Vectorization preserves the Frobenius square",All([B("n",N),B("A",Mat(n))],Eqn(Pow(Norm(Call("vectorize",n,a)),2),Frob(a))),"The Euclidean norm sums the same entries."),
            Item("variance","Cartesian variance",All([B("n",N),B("A",Mat(n)),B("rho",Mat(n))],Eqn(Call("variance",a,rho),var)),
                "“Each modulus builds a different variance, which we’ll distinguish by the corresponding subscript too.” Equation (27), page 17, reads Var∗(X) = Tr[ρ|X|²∗] − |Tr[ρX]|², with subscript C giving |X|²C = (X∗X + XX∗)/2. Here X is A, and the real part makes the real-valued trace explicit.",true,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2009variance"))),
            Item("cartesian","Cartesian quadratic matrix",All([B("n",N),B("A",Mat(n))],Eqn(Call("cartesian",a),cart)),"“For that reason we need a name for the expression ((X∗X + XX∗)/2)1/2, and we have chosen to call it the Cartesian modulus.” (page 17). This definition is the square of that modulus, the literal average of the two Gram matrices.",true,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2009variance"))),
            Item("pure_variance_maximizer","A pure vector attains the density maximum",All([B("n",N),B("A",Mat(n))],Imp(Lt(Num(0),n),
                Ex([B("v",Vec(n))],And(Eqn(Norm(v),Num(1)),All([B("rho",Mat(n))],Imp(Density(rho),LeqF(Call("variance",a,rho),Call("variance",a,pq)))))))),
                "A compact density set supplies a maximum. First-order optimality gives a linear Hermitian maximum; Toeplitz-Hausdorff on its top eigenspace preserves the complex mean while selecting a unit vector.",false,
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/audenaert2009variance"))),
            Item("matrix_pairing","Hilbert-space trace pairing",All([B("n",N),B("A",Mat(n)),B("B",Mat(n))],Eqn(Inner(Call("vectorize",n,a),Call("vectorize",n,b)),Trace(Mul(Adj(a),b)))),"Vectorization realizes the trace inner product."),
            Item("frobSq_star","Conjugate-transpose invariance",All([B("n",N),B("A",Mat(n))],Eqn(Frob(Adj(a)),Frob(a))),"Conjugation preserves squared moduli and transpose permutes entries."),
            Item("trace_product_cauchy","Trace-product Cauchy-Schwarz",All([B("n",N),B("Q",Mat(n)),B("B",Mat(n))],LeqF(Apply(Qualified("Complex","normSq"),Trace(Mul(q,b))),Mul(Frob(q),Frob(b)))),"Apply Hilbert-space Cauchy-Schwarz to Q conjugateTranspose and B."),
            Item("commutator_pure_max_bound","The pure maximum bounds every commutator",All([B("n",N),B("A",Mat(n)),B("v",Vec(n))],
                Imp(And(Eqn(Norm(v),Num(1)),All([B("rho",Mat(n))],Imp(Density(rho),LeqF(Call("variance",a,rho),Call("variance",a,pq))))),
                    All([B("B",Mat(n))],LeqF(Frob(Comm(a,b)),Mul(Mul(Num(4),Frob(b)),Call("variance",a,pq)))))),
                "For nonzero B its two Gram matrices, normalized by twice the Frobenius square, form a density matrix. The commutator variance bound applies to this common density; B equal to zero is included."))));
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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, int p) => new Formula.Power(Parenthesized(a), Num(p));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula Adj(Formula x) => Apply(Qualified("Matrix", "conjTranspose"), x);
    private static Formula Trace(Formula x) => Apply(Qualified("Matrix", "trace"), x);
    private static Formula ReF(Formula x) => Apply(Qualified("Complex", "re"), x);
    private static Formula Frob(Formula x) => Apply(Qualified("RHLinalg", "frobSq"), x);
    private static Formula Comm(Formula a, Formula b) => Call("commutator", a, b);
    private static Formula Smul(Formula c, Formula x) => Seq(c, Cdot, Parenthesized(x));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), C);
    private static Formula Vec(Formula n) => Call("EuclideanSpace", C, Fin(n));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, b);
    private static Formula All(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll, [..vs], b);
    private static Formula Ex(Formula.BoundVariable[] vs, Formula b) => new Formula.BindMany(FormulaQuantifier.Exists, [..vs], b);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula OfLp(Formula v) => Apply(Qualified("WithLp", "ofLp"), v);
    private static Formula Pure(Formula v) => Apply(Qualified("Matrix", "vecMulVec"), OfLp(v), Call("star", OfLp(v)));
    private static Formula Inner(Formula v, Formula w) => Call("inner", C, v, w);
    private static Formula Density(Formula x) => And(Apply(Qualified("Matrix", "PosSemidef"), x), Eqn(Trace(x), Num(1)));
    private static Formula Sum(string i, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(F.Id(i), Colon, type)), Parenthesized(body));
    private static DocumentBlock Item(string name, string title, Formula formula, string explanation,
        bool definition = false, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
