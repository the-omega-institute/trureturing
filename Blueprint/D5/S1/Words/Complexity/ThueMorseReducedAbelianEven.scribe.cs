using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class ThueMorseReducedAbelianEvenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/ThueMorseReducedAbelianEven.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/campbell2025reduced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Thue-Morse letters decide the even-length gap in reduced abelian complexity.",
        H("Even Reduced Abelian Complexity"),
        Blocks(
            Paragraph(Text("Reduced abelian complexity counts the classes of factors of a "
                + "given length, where collapsing each maximal constant run to one letter "
                + "leaves words of equal length that rearrange into one another. For the "
                + "Thue-Morse word the odd lengths already reduce to shorter ones. Campbell, "
                + "Currie and Rampersad displayed a rule for the gap between lengths 4n and "
                + "4n+2 and left it unproved. That rule is proved here.")),
            Paragraph(Text("Indices and counts are natural numbers; the gap is taken in the "
                + "integers and then read by absolute value. The letter t denotes the "
                + "Thue-Morse word indexed from zero, so the two letters compared are at n "
                + "and at 3n. R is the class count carried by the companion module, "
                + "unchanged here. A factor with n edges spans n+1 positions, and its "
                + "alternation count is the number of positions where the letter changes.")),
            Node("minAlternations", "Fewest alternations at a length", MinFormula(),
                "Over all starting positions, the alternation count attains a least value. "
                + "The Thue-Morse word takes only finitely many run patterns at each length, "
                + "so the range is a bounded set of natural numbers and the infimum is "
                + "attained.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("maxAlternations", "Most alternations at a length", MaxFormula(),
                "The same range has a greatest element, attained at some start. The two "
                + "extremes bracket every alternation count occurring at that length.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("alternation_extrema_parity", "Parity of the two extremes", ParityFormula(),
                "Induct strongly on n. Splitting n by parity relates the extremes at n to "
                + "those at half of n, using how the alternation count behaves when one "
                + "letter is appended. The odd branch closes with a fact about three "
                + "consecutive Thue-Morse letters. The statement is the step that carries "
                + "the arithmetic of the word into the counting argument.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("reducedAbelianComplexity_even_difference", "The even-length gap",
                GapFormula(),
                "The alternation counts realised at a fixed length fill an interval, so the "
                + "class count is the size of a weighted interval fixed by the two extremes. "
                + "Moving the length from 4n to 4n+2 shifts that interval by a controlled "
                + "amount, and the gap between the two counts collapses to the difference of "
                + "the extremes taken modulo two. The previous parity statement then decides "
                + "it. The hypothesis on n is needed: at n equal to zero the gap is two.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("campbell-currie-rampersad-eq-11"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("ccr-eq11-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula MinFormula() => Disp(Seq(NatBound("n"), Sp,
        Call("minAlt", N()), Sp, Eq, Sp,
        new Formula.Subscript(Min, StartBound()), Sp, Call("alt", N(), S())));

    private static Formula MaxFormula() => Disp(Seq(NatBound("n"), Sp,
        Call("maxAlt", N()), Sp, Eq, Sp,
        new Formula.Subscript(Max, StartBound()), Sp, Call("alt", N(), S())));

    private static Formula ParityFormula() => Disp(Seq(NatBound("n"), Sp,
        Open, new Formula.Modulo(Add(Call("minAlt", N()), Call("maxAlt", N())), D(2)), Sp,
        Eq, Sp, D(0), Close, Sp, Iff, Sp, SameLetter()));

    private static Formula GapFormula() => Disp(Seq(NatBound("n"), Sp, D(0), Sp, Lt, Sp, N(), Sp,
        Implies, Sp,
        Open, SameLetter(), Sp, Implies, Sp, Gap(), Sp, Eq, Sp, D(0), Close, Sp, Land, Sp,
        Open, DifferentLetter(), Sp, Implies, Sp, Gap(), Sp, Eq, Sp, D(1), Close));

    private static Formula Gap() => new Formula.Absolute(
        Sub(Call("R", Add(Mul(D(4), N()), D(2))), Call("R", Mul(D(4), N()))));

    private static Formula SameLetter() =>
        Seq(Call("t", N()), Sp, Eq, Sp, Call("t", Mul(D(3), N())));

    private static Formula DifferentLetter() =>
        Seq(Call("t", N()), Sp, Neq, Sp, Call("t", Mul(D(3), N())));

    private static Formula StartBound() => Grp(Seq(S(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N"))));

    private static Formula N() => F.Id("n");
    private static Formula S() => F.Id("s");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula NatBound(string name) => Seq(Forall, Sp, F.Id(name), Sp,
        InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma);
}
