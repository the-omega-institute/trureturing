using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CollinearTripleFixedPointCensusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonidentity translations fix precisely the cosets of an admissible three-cycle.",
        H("Collinear Triple Fixed Point Census"),
        Blocks(
            Paragraph(Text("For every positive modulus n, let G(n) be ZMod(n) times ZMod(n). "
                + "Let T(n) consist of unordered finite subsets S of G(n) with exactly three "
                + "elements, with both coordinate projections injective on S, and with the "
                + "following determinant identity for every choice of points in S:")),
            Paragraph(Math(Disp(Seq(Forall, Sp, F.Id("p"), Comma, F.Id("q"), Comma,
                F.Id("r"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                Diff("q", 1, "p"), Diff("r", 2, "p"), Sp, Eq, Sp,
                Diff("r", 1, "p"), Diff("q", 2, "p"))))),
            Paragraph(Text("Write F(n,t) for the members of T(n) fixed by translation by t. "
                + "Addition to a set denotes its pointwise translate; its cardinality counts "
                + "each unordered set once. The identity translation is excluded only from "
                + "the zero-count and quartet assertions. No prime-modulus hypothesis is used.")),
            Paragraph(Text("The displayed floor of n squared divided by three denotes "
                + "natural Euclidean division, with any remainder discarded.")),
            Describe.Lean(
                DescribeId.Create("collinear-triple-fixed-point-census"),
                DeclarationHandle.Create("D5/S3/Factorization/CollinearTripleFixedPointCensus.fixed_point_census"),
                H("Three-cycle classification, exact fibers, and census"),
                StatementSource.FromAuthor(CensusStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If three times t is zero and both coordinates of t are "
                        + "nonzero, each coordinate has additive order three. The set C of "
                        + "its first three multiples consequently has three points and both "
                        + "coordinate maps are injective. Differences of multiples of the "
                        + "same vector have zero determinant, so C belongs to T(n). "
                        + "Translation by t cyclically permutes C.")),
                    Paragraph(Text("If t fixes S, choose p in S. Invariance places all three "
                        + "points of p+C in S; equality follows from their common cardinality "
                        + "three. Conversely, every translate of C is fixed. A translation "
                        + "stabilizes C exactly when its vector belongs to C: necessity follows "
                        + "by translating zero, and sufficiency follows from the cyclic "
                        + "permutation. This gives the displayed exact fibers and a stabilizer "
                        + "of cardinality three. Orbit-stabilizer then gives n squared divided "
                        + "by three fixed triples.")),
                    Paragraph(Text("For any nonzero fixing vector, summing the three points "
                        + "forces three times the vector to vanish. A zero first or second "
                        + "coordinate would contradict the corresponding injectivity, because "
                        + "a nonzero translation cannot fix an individual point. For n=3m, "
                        + "the standard representative of a coordinate annihilated by three "
                        + "is zero, m, or 2m. Keeping both coordinates nonzero gives exactly "
                        + "the four displayed pairs. Every other nonzero translation fixes "
                        + "no member of T(n)."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Grid() => Call("G", V("n"));
    private static Formula Triples() => Call("T", V("n"));
    private static Formula Count() => Call("card", Call("F", V("n"), V("t")));
    private static Formula ThirdSquare() => new Formula.Floor(new Formula.Fraction(
        new Formula.Power(V("n"), D(2)), D(3)));
    private static Formula Coord(string point, byte index) => Seq(V(point), Underscore, Grp(D(index)));
    private static Formula Diff(string point, byte index, string origin) =>
        Seq(Open, Coord(point, index), Minus, Coord(origin, index), Close);
    private static Formula Eligible() => Seq(D(3), V("t"), Sp, Eq, Sp, D(0), Sp, Land, Sp,
        Coord("t", 1), Sp, Neq, Sp, D(0), Sp, Land, Sp, Coord("t", 2), Sp, Neq, Sp, D(0));
    private static Formula Quartet() => Seq(OpenBrace,
        Open, V("m"), Comma, V("m"), Close, Comma,
        Open, V("m"), Comma, D(2), V("m"), Close, Comma,
        Open, D(2), V("m"), Comma, V("m"), Close, Comma,
        Open, D(2), V("m"), Comma, D(2), V("m"), Close, CloseBrace);
    private static Formula CensusStatement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("n"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
            D(0), Sp, Lt, Sp, V("n"), Sp, Implies),
        Seq(Grp(), OpenBracket, Forall, Sp, V("t"), Sp, InMacro, Sp, Grid(), Comma, Sp,
            D(3), V("t"), Sp, Eq, Sp, D(0), Sp, Implies, Sp,
            Coord("t", 1), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
            Coord("t", 2), Sp, Neq, Sp, D(0), Sp, Implies),
        Seq(Exists, Sp, V("C"), Sp, InMacro, Sp, Triples(), Comma, Sp,
            V("C"), Sp, Eq, Sp, OpenBrace, D(0), Comma, V("t"), Comma,
            D(2), V("t"), CloseBrace, Sp, Land),
        Seq(Open, Forall, Sp, V("S"), Sp, InMacro, Sp, Triples(), Comma, Sp,
            Open, V("t"), Plus, V("S"), Sp, Eq, Sp, V("S"), Sp, Iff, Sp,
            Exists, Sp, V("p"), Sp, InMacro, Sp, Grid(), Comma, Sp,
            V("p"), Plus, V("C"), Sp, Eq, Sp, V("S"), Close, Close, Sp, Land),
        Seq(Open, Forall, Sp, V("p"), Comma, V("q"), Sp, InMacro, Sp, Grid(), Comma, Sp,
            Open, V("p"), Plus, V("C"), Sp, Eq, Sp, V("q"), Plus, V("C"), Sp, Iff, Sp,
            V("p"), Minus, V("q"), Sp, InMacro, Sp, V("C"), Close, Close, Sp, Land),
        Seq(Count(), Sp, Eq, Sp, ThirdSquare(), CloseBracket, Sp, Land),
        Seq(Grp(), OpenBracket, Forall, Sp, V("t"), Sp, InMacro, Sp, Grid(), Comma, Sp,
            V("t"), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
            Neg, Open, Eligible(), Close, Sp, Implies, Sp,
            Count(), Sp, Eq, Sp, D(0), CloseBracket, Sp, Land),
        Seq(Grp(), OpenBracket, Forall, Sp, V("m"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
            D(0), Sp, Lt, Sp, V("m"), Sp, Implies, Sp,
            V("n"), Sp, Eq, Sp, D(3), V("m"), Sp, Implies),
        Seq(Forall, Sp, V("t"), Sp, InMacro, Sp, Grid(), Comma, Sp,
            V("t"), Sp, Neq, Sp, D(0), Sp, Implies, Sp, Count(), Sp, Eq, Sp,
            Begin, Grp(V("cases")),
            ThirdSquare(), Amp, V("t"), Sp, InMacro, Sp, Quartet(), RowBreak,
            D(0), Amp, Neg, Open, V("t"), Sp, InMacro, Sp, Quartet(), Close,
            End, Grp(V("cases")), CloseBracket)
    ]));
}
