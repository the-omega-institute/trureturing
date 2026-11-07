using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FixedPoint;

internal sealed class MarkovKakutaniDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/atlas2026markovkakutani");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting continuous affine self-maps of a compact convex set have a common fixed point.",
        H("Markov-Kakutani common fixed point theorem"),
        Blocks(Describe.Lean(
            DescribeId.Create("markov-kakutani-common-fixed-point"),
            DeclarationHandle.Create("D5/S3/Geometry/FixedPoint/MarkovKakutani.exists_common_fixed_point"),
            H("A common fixed point for an arbitrary commuting affine family"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let E be any real normed vector space and K a nonempty compact convex subset. The index type may be empty or infinite. Each F i is a continuous affine map on E that preserves K, and every pair commutes at every point of E. The conclusion gives one point of K fixed by all maps. Neither completeness nor finite dimension is assumed.")),
                Paragraph(Text("For one map T, average the first m iterates of a point of K. Convexity keeps each Cesaro average in K. Affinity and telescoping make its displacement under T equal to the endpoint difference divided by m. Compactness bounds the iterates and supplies a convergent subsequence; the displacement tends to zero, so continuity fixes the limit.")),
                Paragraph(Text("For a finite subfamily, the common fixed locus already obtained is closed and convex. Global commutation makes the next map preserve that locus, so the single-map result extends the fixed family. The finite fixed loci have the finite intersection property inside compact K; their intersection contains a point fixed by every index. The empty index case follows from nonemptiness of K.")),
                Paragraph(Text("This theorem asserts existence only; it supplies no unique point, algorithm or convergence rate."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula E => V("E");
    private static Formula I => V("iota");
    private static Formula K => V("K");
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var n = 0; n < args.Length; n++)
        {
            if (n > 0) items.AddRange([Comma, Sp]);
            items.Add(args[n]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula And(Formula left, Formula right) => Seq(Par(left), Sp, Land, Sp, Par(right));
    private static Formula AffineMapType => Call("ContinuousAffineMap", Real, E, E);
    private static Formula MapAt(Formula index, Formula point) => Call("F", index, point);
    private static Formula Statement()
    {
        var commute = All("i", I, All("j", I, All("x", E,
            Eqn(MapAt(V("i"), MapAt(V("j"), V("x"))),
                MapAt(V("j"), MapAt(V("i"), V("x")))))));
        var fixedPoint = Some("x", E, And(Member(V("x"), K),
            All("i", I, Eqn(MapAt(V("i"), V("x")), V("x")))));
        var family = All("F", new Formula.TypeArrow(I, AffineMapType),
            All("hm", All("i", I, Call("MapsTo", Call("F", V("i")), K, K)),
                All("hcomm", commute, fixedPoint)));
        return All("E", Seq(V("Type"), Star),
            Seq(Inst(Call("NormedAddCommGroup", E)), Inst(Call("NormedSpace", Real, E)),
                All("K", Call("Set", E),
                    All("hn", Seq(Operatorname, Grp(V("Set"), Dot, V("Nonempty")), Open, K, Close),
                        All("hc", Call("IsCompact", K),
                            All("hv", Call("Convex", Real, K),
                                All("iota", Seq(V("Type"), Star), family)))))));
    }
}
