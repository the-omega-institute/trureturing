using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class RiordanBellInertiaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/cheon2018riordanspectral");

    public DocumentDefinition Create()
    {
        Formula n = V("n"), g = V("g"), i = V("i"), j = V("j");
        Formula iv = Call("val", i), jv = Call("val", j);
        Formula entry = All("n", C("Nat"), All("g", Series(),
            All("i", Call("Fin", n), All("j", Call("Fin", n),
                Eqn(Call("adjacency", n, g, i, j),
                    Ite(Lt(jv, iv), Lower(g, iv, jv),
                        Ite(Lt(iv, jv), Lower(g, jv, iv), D(0))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An order-five Bell-type Riordan graph has positive inertia three and negative inertia two.",
            H("Bell-type Riordan adjacency and the inertia question"), Blocks(
                Node("adjacency", "The source coefficient rule", "adjacency", entry,
                    "Definition 2.2 and equation (2), page 3, give r(i,j) congruent modulo 2 to the coefficient of z^(i-2) in g(z)f(z)^(j-1), for source labels 1 <= j < i <= n. Here f=X*g and i in Fin n denotes source label i.val+1. Thus the displayed natural subtraction val(i)-1 is exactly source i-2 on the lower triangle, and val(j) is source j-1. Lower(g,a,b) is expanded in the formula as the real cast of coeff(a-1, g*(X*g)^b) modulo positive two. This remainder is the unique integer in {0,1} congruent to the coefficient. The diagonal is zero and the upper triangle is reflected. The domain is the entire ring PowerSeries Int, with no polynomial degree bound. X*g has zero constant coefficient for every such g.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("claim", "Problem 6.11 in full", "claim", Eqn(Call("claim"), Par(ClaimBody())),
                    "Problem 6.11, page 25: Is it true that n+ <= n- for any Riordan graph G_n(g,zg)? Every positive order n and every integer formal power series g is quantified. The displayed positive and negative indices are RHLinalg.posIndex and RHLinalg.negIndex applied to the canonical Hermitian proof for adjacency n g. They count eigenvalues strictly above and strictly below zero. Mathlib's Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies the full indexed eigenvalue multiset with characteristic roots, so these are algebraic multiplicities and zero contributes to neither count. No properness, evenness, io-decomposability, nonsingularity or finite-order restriction is assumed.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("result", "The order-five counterexample", "result", Seq(Neg, Sp, Par(ClaimBody())),
                    "Set n=5 and g=1+X^3 in PowerSeries Int. Direct coefficient multiplication gives lower rows (1), (0,1), (0,0,1), (1,0,0,1), before reduction modulo two. The adjacency rows are (0,1,0,0,1), (1,0,1,0,0), (0,1,0,1,0), (0,0,1,0,1), (1,0,0,1,0). Let B have rows (1,1,-1,-1,1), (1,-1,0,0,-1), (0,0,1,1,-1), (0,0,1,-1,1), (0,0,0,0,1). Exact finite matrix arithmetic gives det B=4 and B transpose times A times B = diagonal(2,-2,2,-2,2). Apply D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det, then D5.S3.QuadraticForms.StructuredRankOneInertia.diagonal_counts. The indices are therefore 3 and 2, contradicting the universal inequality. The coefficient-to-adjacency equality is proved from the source series, rather than assumed from the cycle graph. The counterexample uses no restriction on the universal input domain.",
                    DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    }

    private static Formula Series() => Call("PowerSeries", C("Int"));
    private static Formula Lower(Formula g, Formula a, Formula b) =>
        Par(Seq(new Formula.Modulo(Call("coeff", Sub(a, D(1)),
            Mul(g, new Formula.Power(Par(Mul(C("X"), g)), b))), D(2)), Colon, Sp, C("Real")));
    private static Formula ClaimBody() => All("n", C("Nat"),
        new Formula.Logic(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, V("n")), FormulaLogicOperator.Implies,
            All("g", Series(), Rel(Index(true), FormulaRelationOperator.LessThanOrEqual, Index(false)))));
    private static Formula Index(bool positive) => Call(positive ? "posIndex" : "negIndex",
        Call("adjacency", V("n"), V("g")));
    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("riordan-bell-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? C(name) : new Formula.Apply(C(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Ite(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
}
