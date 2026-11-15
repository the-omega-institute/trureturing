using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class RankBoundedChordalPsdCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clique-positive real tables on finite chordal graphs have PSD completions with the same local rank bound.",
        H("Rank-Bounded Positive Semidefinite Completion on Chordal Graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("rank-bounded-chordal-psd-completion"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/RankBoundedChordalPsdCompletion.exists_posSemidef_completion_rank_le"),
            H("Every diagonal and graph edge is preserved"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/laurentvarvitsiotis2014boundedrank")),
            Blocks(
                Paragraph(Text("Let V be any finite type in any universe, d any natural number, G a chordal simple graph on V, and A any real matrix on V. For every clique C, assume the principal block Restrict(A,C) is positive semidefinite and has real matrix rank at most d. Then a real matrix B on V exists which is positive semidefinite, has real matrix rank at most d, and agrees with A on every diagonal and graph edge. Restrict denotes Matrix.submatrix with both maps the subtype inclusion. Cliques include the empty set and singletons; d may be zero.")),
                Paragraph(Text("Laurent and Varvitsiotis state the minimum-rank chordal completion result in their introduction. Their Lemma 2 proof explains the orthogonal alignment on an overlap. This is established mathematics. Unspecified nonedge input entries may be nonsymmetric, and no global completion or realization is given as a premise.")),
                Paragraph(Text("Remove a simplicial vertex v using the finite chordal Dirac theorem. Induction realizes the remaining graph in the unchanged Euclidean space with d coordinates. The clique consisting of v and its neighbours has a Gram factor in that same space because its PSD rank is at most d. The local and old neighbour vectors have equal pairwise inner products. An ambient linear isometric equivalence carries the local neighbours to the old neighbours. Apply it to the local vector for v and leave every old vector unchanged. Inner products with every neighbour, and the prescribed diagonal at v, are preserved. Taking the Gram matrix gives positivity; a factor with d rows bounds its rank by d.")),
                Paragraph(Text("The local rank factorization and equal-Gram ambient isometry are adapted from TauCetiProject/TauCeti at revision 0ae45cec5df3d83669e6a8403d229ddbf562d89c. The precise consumed sources, original authors and Apache license are identified in the cited literature note and the Lean source. The alignment includes dependent, zero and empty families. It needs no inverse of an overlap Gram matrix and adds no residual coordinate. Empty carriers, isolated vertices, disconnected graphs and singular clique blocks remain in scope.")),
                Paragraph(Text("For a conditional fixed-dimension model, put d=3 or d=6 and prescribe diagonal one. Assume the full local PSD and rank bound on every clique; a clique-size bound is not substituted for the rank premise. The resulting completion has a common real Gram realization in that fixed dimension, and every vector has norm one. Every specified edge retains its input inner product. This asserts existence, without uniqueness, dynamics or a choice of realization supplied in advance."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var v = F.Id("V"); var g = F.Id("G"); var a = F.Id("A");
        var d = F.Id("d"); var b = F.Id("B"); var c = F.Id("C"); var i = F.Id("i"); var j = F.Id("j");
        var matrix = Call("Matrix", v, v, Seq(Mathbb, Grp(F.Id("R"))));
        var cliquePositive = All(c, Call("Set", v), Seq(
            Call("IsClique", g, c), Sp, Rightarrow, Sp,
            Call("PosSemidef", Call("Restrict", a, c)), Sp, Land, Sp,
            Call("rank", Call("Restrict", a, c)), Sp, Leq, Sp, d));
        var agreement = All(i, v, All(j, v, Seq(
            Open, i, Sp, Eq, Sp, j, Sp, Lor, Sp, Call("Adj", g, i, j), Close,
            Sp, Rightarrow, Sp, Call("entry", b, i, j), Sp, Eq, Sp, Call("entry", a, i, j))));
        return All(v, F.Id("Type"), Seq(OpenBracket, Call("Finite", v), CloseBracket, Sp,
            All(d, Seq(Mathbb, Grp(F.Id("N"))), All(g, Call("SimpleGraph", v), All(a, matrix, Seq(
                Open, Call("IsChordal", g), Sp, Land, Sp, cliquePositive, Close,
                Sp, Rightarrow, Sp, Some(b, matrix, Seq(
                    Call("PosSemidef", b), Sp, Land, Sp, Call("rank", b), Sp, Leq, Sp, d,
                    Sp, Land, Sp, agreement))))))));
    }

    private static Formula Typed(Formula name, Formula type) => Seq(Open, name, Sp, Colon, Sp, type, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
}
