using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SelfReferentialQuotientFirstOccurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/alkan2020a335925");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first occurrences in Alkan's self-referential quotient recurrence are A000522 thresholds.",
        H("First Occurrences in a Self-Referential Quotient Recurrence"),
        Blocks(
            Node("a", "Alkan's recurrence", SequenceFormula(),
                "The source sequence begins at index one. The formal definition assigns a(0)=1 "
                + "only as a sentinel that totalizes the recursion; this value is not part of the "
                + "source assertion. For every n>=2, the recursive argument is strictly below n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T", "The A000522 thresholds", ThresholdFormula(),
                "This recurrence is A000522, beginning with 1, 2, 5, 16, 65, 326, and 1957.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("alkan_a335925", "Alkan's first-occurrence conjecture", TheoremFormula(),
                "For every positive m, the threshold T(m-1) carries m. Any positive index k "
                + "carrying m is at least that threshold. A two-step induction on threshold blocks "
                + "shows that a(T(r))=r+1, that values on [T(r),T(r+1)) belong to {r,r+1}, "
                + "and that an occurrence of r in this block lies below r*T(r). These bounds give "
                + "both the hit and its minimality.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a335925-self-referential-quotient-first-occurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a335925-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var predecessor = Subtract(n, D(1));
        var recursiveIndex = Floor(Fraction(predecessor, Call("a", predecessor)));
        var initial = Equal(Call("a", D(1)), D(1));
        var recurrence = Universal(n, Seq(
            D(2), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            Equal(Call("a", n), Add(Call("a", recursiveIndex), D(1)))));
        return Disp(Seq(Parenthesized(initial), Sp, Land, Sp, Parenthesized(recurrence)));
    }

    private static Formula ThresholdFormula()
    {
        var r = F.Id("r");
        var successor = Add(r, D(1));
        var initial = Equal(Call("T", D(0)), D(1));
        var recurrence = Universal(r, Equal(
            Call("T", successor), Add(Multiply(successor, Call("T", r)), D(1))));
        return Disp(Seq(Parenthesized(initial), Sp, Land, Sp, Parenthesized(recurrence)));
    }

    private static Formula TheoremFormula()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var threshold = Call("T", Subtract(m, D(1)));
        var hit = Equal(Call("a", threshold), m);
        var minimal = Universal(k, Seq(
            D(1), Sp, Le, Sp, k, Sp, Rightarrow, Sp,
            Equal(Call("a", k), m), Sp, Rightarrow, Sp,
            threshold, Sp, Le, Sp, k));
        return Disp(Universal(m, Seq(
            D(1), Sp, Le, Sp, m, Sp, Rightarrow, Sp,
            Parenthesized(Seq(hit, Sp, Land, Sp, minimal)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(Formula variable, Formula body) => Seq(
        Forall, Sp, variable, Sp, InMacro, Sp, Naturals(), Comma, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Floor(Formula value) => Seq(Lfloor, value, Rfloor);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
