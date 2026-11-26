using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class NotikSingerChamberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/notik2026singergolomb");
    private static readonly LibraryNoteRef Singer =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/singer1938projective");

    private static readonly Formula Naturals = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Reals = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Marks = Call("Fin", Seq(F.Id("m"), Plus, F.D(1)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cyclic perfect difference set cut at a largest gap gives the unique shortest ruler in its normalized real chamber.",
        H("Largest-gap cuts and real Golomb chambers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("notik-singer-cyclic-perfect-difference"),
                DeclarationHandle.Create(Prefix + "CyclicPerfectDifference"),
                H("Unique labelled cyclic differences"), StatementSource.FromAuthor(PerfectDifferenceFormula()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For natural numbers m and N and natural marks x indexed by Fin (m + 1), "
                    + "every natural d with 0 < d < N has exactly one ordered pair (i, j) of "
                    + "distinct indices whose signed integer difference x(j) − x(i) is congruent "
                    + "to d modulo N in Int.ModEq. The labels and their order are part of the witness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("notik-singer-chamber"),
                DeclarationHandle.Create(Prefix + "Chamber"),
                H("The normalized real chamber"), StatementSource.FromAuthor(ChamberFormula()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "For natural reference marks x and real marks y on the same Fin (m + 1), "
                    + "the chamber requires y(0) = 0 and y(j) − y(i) ≥ 1 for every i < j. "
                    + "For every i < j and k < l, whenever the reference natural distance "
                    + "x(j) − x(i) is strictly smaller than x(l) − x(k), the corresponding "
                    + "real distances satisfy y(j) − y(i) + 1 ≤ y(l) − y(k)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("notik-singer-chamber-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Unique shortest ruler after a largest-gap cut"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source, Singer), Blocks(
                    Paragraph(Text(
                        "Let m > 0, let x be strictly increasing natural marks on Fin (m + 1) with "
                        + "x(0) = 0, and write L for the last mark. Let G > 0 be a natural number "
                        + "with every adjacent gap of x at most G. Assume CyclicPerfectDifference "
                        + "for x modulo L + G, so G is a largest cyclic gap and ties are allowed. "
                        + "Equal ordinary distances for i < j and k < l imply (i, j) = (k, l). "
                        + "The real cast of x belongs to its chamber. Every real y in that chamber "
                        + "whose last mark is at most L equals x pointwise after casting. The formula "
                        + "writes casts as type ascriptions and uses natural subtraction for x-distances.")),
                    Paragraph(Text(
                        "Each positive residue below G occurs as a forward distance because a "
                        + "wrapped difference is at least G. Induction using the chamber inequalities "
                        + "bounds every retained gap below by its reference value. The markwise "
                        + "deviations are therefore nondecreasing, and the two endpoint conditions "
                        + "force them all to be zero.")),
                    Paragraph(Text(
                        "Lean checks chamber uniqueness for every cyclic perfect difference set "
                        + "with a largest-gap cut. For any prime power m, the classical Singer "
                        + "construction supplies m + 1 marks modulo N = m² + m + 1 whose ordered "
                        + "differences cover each nonzero residue exactly once. Unit multiplication "
                        + "permutes the differences and translation preserves them. Translate the "
                        + "first mark after any largest gap G to zero and sort the representatives "
                        + "in [0, N). This gives the required increasing marks, with last mark N − G "
                        + "and all retained gaps at most G. This classical specialization proves "
                        + "Notik’s §7 conjecture. The Lean theorem assumes the perfect difference "
                        + "property and compares lengths within one chamber."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("notik-singer-chamber"), ResolutionKind.Proved)))));

    private static Formula PerfectDifferenceFormula()
    {
        Formula x = F.Id("x"), n = F.Id("N"), d = F.Id("d"), p = F.Id("p");
        Formula first = Seq(p, Dot, F.D(1)), second = Seq(p, Dot, F.D(2));
        return DisplayRows(
            Seq(Amp, Forall, Sp, Binder(Naturals, "m"), Sp, Binder(FunctionTo(Naturals), "x"),
                Sp, Binder(Naturals, "N"), Comma),
            Seq(Amp, Call("CyclicPerfectDifference", x, n), Sp, Iff, Sp,
                Forall, Sp, Binder(Naturals, "d"), Comma, Sp,
                F.D(0), Sp, Lt, Sp, d, Sp, To, Sp, d, Sp, Lt, Sp, n, Sp, To),
            Seq(Amp, Quad, Exists, Bang, Sp, Binder(Seq(Marks, Sp, Times, Sp, Marks), "p"), Comma, Sp,
                first, Sp, Neq, Sp, second, Sp, Land, Sp,
                Cast(Mark(x, second), Integers), Sp, Minus, Sp, Cast(Mark(x, first), Integers),
                Sp, Equiv, Sp, Cast(d, Integers), Sp, Pmod, Grp(Cast(n, Integers))));
    }

    private static Formula ChamberFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k"), l = F.Id("l");
        return DisplayRows(
            Seq(Amp, Forall, Sp, Binder(Naturals, "m"), Sp, Binder(FunctionTo(Naturals), "x"),
                Sp, Binder(FunctionTo(Reals), "y"), Comma),
            Seq(Amp, Call("Chamber", x, y), Sp, Iff, Sp, Mark(y, F.D(0)), Sp, F.Eq, Sp, F.D(0), Sp, Land),
            Seq(Amp, Quad, Parens(Seq(Forall, Sp, Binder(Marks, "i", "j"), Comma, Sp,
                i, Sp, Lt, Sp, j, Sp, To, Sp, F.D(1), Sp, Leq, Sp, Distance(y, i, j))), Sp, Land),
            Seq(Amp, Quad, Open, OrderedPairs(i, j, k, l),
                Distance(x, i, j), Sp, Lt, Sp, Distance(x, k, l), Sp, To),
            Seq(Amp, Quad, Quad, Sp, Distance(y, i, j), Sp, Plus, Sp, F.D(1),
                Sp, Leq, Sp, Distance(y, k, l), Close));
    }

    private static Formula ResultFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), g = F.Id("G"), y = F.Id("y");
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k"), l = F.Id("l");
        Formula last = Seq(Named("Fin"), Dot, Call("last", m));
        return DisplayRows(
            Seq(Amp, Forall, Sp, Binder(Naturals, "m"), Sp, Binder(FunctionTo(Naturals), "x"),
                Sp, Binder(Naturals, "G"), Comma),
            Seq(Amp, Quad, F.D(0), Sp, Lt, Sp, m, Sp, To, Sp,
                Mark(x, F.D(0)), Sp, F.Eq, Sp, F.D(0), Sp, To, Sp,
                Call("StrictMono", x), Sp, To, Sp, F.D(0), Sp, Lt, Sp, g, Sp, To),
            Seq(Amp, Quad, Parens(Seq(Forall, Sp, Binder(Call("Fin", m), "i"), Comma, Sp,
                Distance(x, Seq(i, Dot, Named("castSucc")), Seq(i, Dot, Named("succ"))), Sp, Leq, Sp, g)),
                Sp, To, Sp, Call("CyclicPerfectDifference", x, Seq(Mark(x, last), Sp, Plus, Sp, g)), Sp, To),
            Seq(Amp, Quad, Open, OrderedPairs(i, j, k, l),
                Distance(x, i, j), Sp, F.Eq, Sp, Distance(x, k, l), Sp, To, Sp,
                Parens(Seq(i, Comma, Sp, j)), Sp, F.Eq, Sp, Parens(Seq(k, Comma, Sp, l)), Close, Sp, Land),
            Seq(Amp, Quad, Sp, Call("Chamber", x, Seq(LambdaLower, Sp, i, Sp, Mapsto, Sp, Cast(Mark(x, i), Reals))),
                Sp, Land, Sp, Open, Forall, Sp, Binder(FunctionTo(Reals), "y"), Comma, Sp,
                Call("Chamber", x, y), Sp, To, Sp, Mark(y, last), Sp, Leq, Sp, Cast(Mark(x, last), Reals), Sp, To),
            Seq(Amp, Quad, Quad, Forall, Sp, Binder(Marks, "i"), Comma, Sp,
                Mark(y, i), Sp, F.Eq, Sp, Cast(Mark(x, i), Reals), Close));
    }

    private static Formula DisplayRows(params Formula[] rows) => Disp(new Formula.Aligned([.. rows]));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Mark(Formula marks, Formula index) => new Formula.Apply(marks, [index]);
    private static Formula Distance(Formula marks, Formula i, Formula j) =>
        Seq(Mark(marks, j), Sp, Minus, Sp, Mark(marks, i));
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parens(Seq(value, Sp, Colon, Sp, type));
    private static Formula Binder(Formula type, params string[] names) =>
        Parens(Seq([.. names.SelectMany(name => new[] { F.Id(name), Sp }), Colon, Sp, type]));
    private static Formula FunctionTo(Formula type) => Seq(Marks, Sp, To, Sp, type);
    private static Formula OrderedPairs(Formula i, Formula j, Formula k, Formula l) =>
        Seq(Forall, Sp, Binder(Marks, "i", "j", "k", "l"), Comma, Sp,
            i, Sp, Lt, Sp, j, Sp, To, Sp, k, Sp, Lt, Sp, l, Sp, To, Sp);
}
