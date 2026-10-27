using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SpeziaPerimeterHigherExteriorTracesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/spezia2019a330700");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Higher exterior traces of the Spezia perimeter matrix vanish.",
        H("Higher exterior traces of the perimeter matrix"),
        Blocks(
            Node("M", "The perimeter matrix", MatrixFormula(),
                "OEIS A330287, COMMENTS, revision 31 (unpaginated): “The matrix M(n) is defined as M[i,j,n] = i*j if i < 3 or j < 3 and M[i,j,n] = 2*(i + j) - 4 otherwise.” "
                + "The row and column types are Fin n; source indices are val(i)+1 and val(j)+1. "
                + "Entries lie in ℂ. The casts shown in the formula embed natural numbers in ℂ; the comparisons use natural numbers and the subtraction uses ℂ.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Spezia's second exterior-trace conjecture",
                Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A330700, COMMENTS, revision 23, second line of the Conjectures block (unpaginated): “For k > 2, the trace of the k-th exterior power of M(n) is equal to zero.” "
                + "Here n is any positive natural number and k is any natural number greater than two. "
                + "The existing compoundMatrix is the matrix of the exterior power: its entries are determinants of the ordered k-by-k submatrices. "
                + "Matrix.trace sums its diagonal entries. For k > n its index type is empty, so this includes the zero-dimensional exterior space.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All exterior traces above order two vanish", Disp(ClaimBody()),
                "Write v(i)=val(i)+1 and w(i)=max(val(i)−1,0), interpreted in ℂ. "
                + "The entry formula gives M(n)=vvᵀ−wwᵀ, hence a product of an n-by-two matrix and a two-by-n matrix. "
                + "For k > 2, Cauchy–Binet expresses every k-by-k minor as a sum over k-element subsets of Fin 2. "
                + "There are no such subsets. Thus the whole higher compound matrix is zero, and taking its trace gives zero. "
                + "The assertion concerns the second conjecture; the separate scalar sequence and its second-exterior-trace conjecture are separate questions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("spezia-perimeter-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            null);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula MatrixFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        var iv = Call("val", i);
        var jv = Call("val", j);
        var ic = Add(Parenthesized(Seq(App(Q("Nat", "cast"), iv), Colon, Sp, Complex)), D(1));
        var jc = Add(Parenthesized(Seq(App(Q("Nat", "cast"), jv), Colon, Sp, Complex)), D(1));
        var condition = new Formula.Logic(
            Lt(Add(iv, D(1)), D(3)), FormulaLogicOperator.Or, Lt(Add(jv, D(1)), D(3)));
        var body = Seq(Operatorname, Grp(F.Id("if")), Sp, condition, Sp,
            Operatorname, Grp(F.Id("then")), Sp,
            Multiply(Parenthesized(ic), Parenthesized(jc)), Sp,
            Operatorname, Grp(F.Id("else")), Sp,
            Subtract(Multiply(D(2), Parenthesized(Add(Parenthesized(ic), Parenthesized(jc)))), D(4)));
        return Disp(All("n", Nat, Equal(Call("M", n),
            Fn("i", Call("Fin", n), Fn("j", Call("Fin", n), body)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var trace = App(Q("Matrix", "trace"), Call("compoundMatrix", Call("M", n), k));
        return All("n", Nat, Imp(Lt(D(0), n),
            All("k", Nat, Imp(Lt(D(2), k), Equal(trace, D(0))))));
    }
}
