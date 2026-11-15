using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class ChordalPsdCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clique-positive real tables on finite chordal graphs have positive semidefinite completions, including singular blocks.",
        H("Real Positive Semidefinite Completion on Chordal Graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("chordal-psd-completion"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/ChordalPsdCompletion.exists_posSemidef_completion"),
            H("Every diagonal and graph edge is preserved"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/vandenbergheandersen2015chordal")),
            Blocks(
                Paragraph(Text("Let V be any finite type, in any universe, G a simple graph on V, and A a real matrix indexed by V. Assume G is chordal and the principal restriction of A to every clique C is positive semidefinite. There exists a real positive semidefinite matrix B on the same V with B(i,j)=A(i,j) whenever i=j or G has the edge i,j. Restrict(A,C) in the formula is Matrix.submatrix A Subtype.val Subtype.val, indexed by the subtype of vertices in C. Cliques include singletons and the empty set.")),
                Paragraph(Text("This is the positive semidefinite existence direction of Vandenberghe and Andersen's Theorem 10.1, printed page 356. It is established mathematics, not an originality or open-problem claim. The real table A need not be symmetric on unspecified nonedges. The assumptions impose the required symmetry on each specified clique; B is symmetric everywhere. There is no constraint on the unspecified nonedge entries of B.")),
                Paragraph(Text("Strong induction on the number of vertices uses SimpleGraph.IsChordal.exists_isSimplicial and IsChordal.induce from the existing Dirac module. Remove a simplicial vertex v and recursively complete the induced graph. Its positive semidefinite completion has a real Gram factor x. The clique consisting of v and its neighbours has a separate real Gram factor y. Both factors come directly from Matrix.posSemidef_iff_eq_sum_vecMulVec, which includes singular matrices.")),
                Paragraph(Text("On the neighbours, the two Gram families agree because their entries come from the same A. The original WeightedGramContraction.contraction_of_gram supplies a contraction Z carrying each local neighbour vector to its old vector. Equality of neighbour norms implies Z-adjoint x(k)=y(k), so the candidate Z(y(v)) has every required mixed inner product. Its norm can be smaller than the prescribed norm. Embed the old space as the first factor of its L2 product with the reals, and give the new vertex the extra coordinate sqrt(norm(y(v))^2-norm(Z(y(v)))^2). Contractivity makes this real; its square restores the prescribed diagonal. The Gram matrix of this combined family is the completion.")),
                Paragraph(Text("A separate conditional finite-memory model fixes natural numbers N and M and one real table A on vertices 0 through N, with diagonal one. Assume each consecutive window [a,a+M] intersected with this horizon has a positive semidefinite principal block. Retain precisely the pairs with absolute index difference at most M, including the diagonal. This band graph has the natural index order as a perfect elimination order: two later neighbours of the same vertex differ by at most M. Every nonempty clique lies in the window starting at its least index; the empty clique is harmless. The theorem therefore supplies a PSD completion, and the actual real Gram factor supplies a common finite-dimensional family p with norm(p(i))=1 and inner(p(i),p(j))=A(i,j) for every retained pair. Positivity of shorter consecutive windows follows by principal restriction. Overlap agreement comes from using one table, not separate unrelated realizations.")),
                Paragraph(Text("This is an explicitly added conditional model motivated by finite-memory windows, not a requirement already stated by existing vector presets. The band application reuses the general theorem. It asserts neither a fixed dimension such as three or six, uniqueness, dynamics, interior slack nor an infinite extension. N=0, M=0 and singular windows are included. A separate boundary check uses the specified entries d(i)d(j) for an arbitrary real family d and arbitrary chordal graph, while putting -100 on every unspecified nonedge of the input table. Clique restrictions are rank-one Gram matrices, including zero and singular cases; the output preserves only the prescribed entries.")),
                Paragraph(Text("The empty carrier uses the empty zero matrix. An isolated eliminated vertex has an empty neighbour family, and disconnected graphs require no connectedness assumption. Zero residuals and singular neighbour blocks are allowed. No inverse, positive definiteness, nonsingular separator, prescribed rank, supplied global completion or fixed ambient dimension is assumed."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var v = F.Id("V"); var g = F.Id("G"); var a = F.Id("A");
        var b = F.Id("B"); var c = F.Id("C"); var i = F.Id("i"); var j = F.Id("j");
        var matrix = Call("Matrix", v, v, Seq(Mathbb, Grp(F.Id("R"))));
        var cliquePositive = All(c, Call("Set", v), Seq(
            Call("IsClique", g, c), Sp, Rightarrow, Sp,
            Call("PosSemidef", Call("Restrict", a, c))));
        var agreement = All(i, v, All(j, v, Seq(
            Open, i, Sp, Eq, Sp, j, Sp, Lor, Sp, Call("Adj", g, i, j), Close,
            Sp, Rightarrow, Sp, Call("entry", b, i, j), Sp, Eq, Sp, Call("entry", a, i, j))));
        return All(v, F.Id("Type"), Seq(OpenBracket, Call("Finite", v), CloseBracket, Sp,
            All(g, Call("SimpleGraph", v), All(a, matrix, Seq(
                Open, Call("IsChordal", g), Sp, Land, Sp, cliquePositive, Close,
                Sp, Rightarrow, Sp, Some(b, matrix, Seq(
                    Call("PosSemidef", b), Sp, Land, Sp, agreement)))))));
    }

    private static Formula Typed(Formula name, Formula type) => Seq(Open, name, Sp, Colon, Sp, type, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
}
