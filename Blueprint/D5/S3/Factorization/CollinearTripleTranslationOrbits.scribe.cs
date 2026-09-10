using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class CollinearTripleTranslationOrbitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/CollinearTripleTranslationOrbits.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2025a146557");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation orbits prove the square-divisibility conjecture in OEIS A146557.",
        H("Collinear Triple Translation Orbits"),
        Blocks(
            Paragraph(Text("Peter Bala's July 24, 2025 conjecture concerns unordered triples "
                + "of points modulo n. No two points may have the same first coordinate or "
                + "the same second coordinate. Collinearity means the difference determinant "
                + "vanishes modulo n, including when n is composite.")),
            Node("Point", "The square grid", Disp(Seq(Call("Point", N()), Sp, Eq, Sp,
                Call("ZMod", N()), Sp, Times, Sp, Call("ZMod", N()))),
                "Both coordinates lie in the ring of integers modulo n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsCollinearTriple", "Admissible three-element sets", TriplePredicate(),
                "The two coordinate projections are injective on S. The determinant "
                + "identity is required for every p, q, r in S; repeated points satisfy it "
                + "automatically, and permuting distinct points preserves its vanishing.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Triple", "The objects being counted", Disp(Seq(Call("Triple", N()), Sp,
                Eq, Sp, OpenBrace, Sp, F.Id("S"), Sp, InMacro, Sp,
                Call("Finset", Call("Point", N())), Sp, Mid, Sp,
                Call("IsCollinearTriple", F.Id("S")), Sp, CloseBrace)),
                "An object is a finite set, not an ordered tuple. Its cardinal condition "
                + "is exactly three, so each unordered configuration contributes once.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("square_dvd_card_collinear_triples", "The A146557 divisibility conjecture",
                Disp(Seq(Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Sp, Lt, Sp, N(), Sp, Implies, Sp,
                    Neg, Sp, Open, D(3), Sp, Mid, Sp, N(), Close, Sp, Implies, Sp,
                    new Formula.Power(N(), D(2)), Sp, Mid, Sp, Call("card", Call("Triple", N())))),
                "Translation preserves coordinate injectivity and every coordinate difference, "
                + "so it acts on these sets. If translation by t fixes S, summing its three "
                + "elements before and after translation gives sum(S)=3t+sum(S), hence 3t=0. "
                + "Since 3 is coprime to n, it is a unit modulo n, and both coordinates of t "
                + "are zero. The action is therefore free. The standard free-action "
                + "equivalence identifies the set of configurations with its orbit quotient "
                + "times the translation group. The latter has n squared elements, proving "
                + "the divisibility for every positive n not divisible by three.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a146557-collinear-triple-divisibility"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("triple-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Coord(string point, byte index) =>
        Seq(F.Id(point), Underscore, Grp(D(index)));
    private static Formula Difference(string a, byte i, string b) =>
        Seq(Open, Coord(a, i), Minus, Coord(b, i), Close);
    private static Formula TriplePredicate() => Disp(new Formula.Aligned([
        Seq(Call("IsCollinearTriple", F.Id("S")), Sp, Iff, Sp,
            Call("card", F.Id("S")), Sp, Eq, Sp, D(3), Sp, Land),
        Seq(Call("InjOn", F.Id("fst"), F.Id("S")), Sp, Land, Sp,
            Call("InjOn", F.Id("snd"), F.Id("S")), Sp, Land),
        Seq(Forall, Sp, F.Id("p"), Comma, F.Id("q"), Comma, F.Id("r"), Sp,
            InMacro, Sp, F.Id("S"), Comma, Sp,
            Difference("q", 1, "p"), Difference("r", 2, "p"), Sp, Eq, Sp,
            Difference("r", 1, "p"), Difference("q", 2, "p"))
    ]));
}
