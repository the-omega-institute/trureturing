using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class RestrictedGrowthLabelOccurrencesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/RestrictedGrowthLabelOccurrences.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mathar2016a270236");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricted-growth words give Mathar's two closed label-occurrence counts.",
        H("Label Occurrences in Restricted-Growth Words"),
        Blocks(
            Paragraph(Text(
                "Words are lists of natural labels stored in reverse chronological order. "
                + "The first generated label is 1, and each next label lies from 1 through "
                + "one more than the maximum already present. T(n,p) sums the number of "
                + "occurrences of label p over all words of length n.")),
            Paragraph(Text(
                "All arithmetic in the two closed forms is natural-number arithmetic. "
                + "Subtraction is truncated natural subtraction. Each slash denotes the "
                + "natural-number quotient, not rational division or a displayed fraction.")),
            Node("maxLabel", "Largest label", MaxLabelFormula(),
                "Folding maximum from zero returns the largest label, with value zero on "
                + "the empty word.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("words", "Restricted-growth words", WordsFormula(),
                "The recurrence starts from the empty word. Each step prepends every label "
                + "in the inclusive interval from 1 to one above the previous maximum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T", "Total label occurrences", TFormula(),
                "For every length and label, this definition sums List.count over the "
                + "finite set of restricted-growth words.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("mathar_f1", "The penultimate-label formula", FirstFormula(),
                "The all-distinct word and the one-repeat maximum layer give one base "
                + "occurrence, one occurrence for each chosen repeat pair, and one extra "
                + "occurrence when the repeated label is the penultimate label.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a270236-rgf-penultimate-label-count"),
                    ResolutionKind.Proved)),
            Node("mathar_f2", "The antepenultimate-label formula", SecondFormula(),
                "The label-extension sum separates the top three maximum layers. The "
                + "two-repeat layer consists of one triple block or two paired blocks; "
                + "the resulting binomial expression normalizes to the quotient by 24.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a270236-rgf-antepenultimate-label-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a270236-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula MaxLabelFormula()
    {
        var w = F.Id("w");
        return Disp(new Formula.Aligned([
            Seq(F.Id("maxLabel"), Colon, Sp, Lists(), Sp, To, Sp, Naturals()),
            Universal(w, Lists(), Equal(MaxLabel(w), Call("foldr", F.Id("max"), D(0), w)))
        ]));
    }

    private static Formula WordsFormula()
    {
        var n = F.Id("n");
        var w = F.Id("w");
        var x = F.Id("x");
        var nextLabels = Call("Icc", D(1), Add(MaxLabel(w), D(1)));
        var extensions = Call("image", nextLabels,
            Lambda(x, Call("cons", x, w)));
        return Disp(new Formula.Aligned([
            Seq(F.Id("words"), Colon, Sp, Naturals(), Sp, To, Sp, FiniteLists()),
            Equal(Words(D(0)), Seq(OpenBrace, EmptyList(), CloseBrace)),
            Universal(n, Naturals(), Equal(Words(Add(n, D(1))),
                Call("biUnion", Words(n), Lambda(w, extensions))))
        ]));
    }

    private static Formula TFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var w = F.Id("w");
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(w, Sp, InMacro, Sp, Words(n))), Sp, Call("count", w, p));
        return Disp(new Formula.Aligned([
            Seq(F.Id("T"), Colon, Sp, Naturals(), Sp, To, Sp,
                Naturals(), Sp, To, Sp, Naturals()),
            Universal(n, Naturals(), Universal(p, Naturals(),
                Equal(Call("T", n, p), sum)))
        ]));
    }

    private static Formula FirstFormula()
    {
        var n = F.Id("n");
        var numerator = Multiply(n, Parenthesized(Subtract(n, D(1))));
        return Universal(n, Naturals(), Seq(D(1), Sp, Lt, Sp, n, Sp, Implies, Sp,
            Equal(Call("T", n, Subtract(n, D(1))),
                Add(D(2), NaturalQuotient(numerator, D(2))))));
    }

    private static Formula SecondFormula()
    {
        var n = F.Id("n");
        var polynomial = Add(Subtract(Multiply(D(3), Power(n, D(2))),
            Multiply(D(5), n)), D(2, 6));
        var numerator = Multiply(Multiply(n, Add(n, D(1))),
            Parenthesized(polynomial));
        return Universal(n, Naturals(), Seq(D(1), Sp, Lt, Sp, n, Sp, Implies, Sp,
            Equal(Call("T", Add(n, D(1)), Subtract(n, D(1))),
                Add(D(2), NaturalQuotient(numerator, D(2, 4))))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Lists() => Call("List", Naturals());
    private static Formula FiniteLists() => Call("Finset", Lists());
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula MaxLabel(Formula w) => Call("maxLabel", w);
    private static Formula Words(Formula n) => Call("words", n);
    private static Formula Universal(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(LambdaLower, Sp, variable, Comma, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NaturalQuotient(Formula left, Formula right) =>
        Seq(left, Sp, Slash, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.Add(Comma);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
