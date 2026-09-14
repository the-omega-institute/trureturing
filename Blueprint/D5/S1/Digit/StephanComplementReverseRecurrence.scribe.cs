using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class StephanComplementReverseRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/StephanComplementReverseRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/stephan2003a059894");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stephan's binary complement-reversal recurrences and digit-count identities hold for all positive inputs.",
        H("Stephan's Complement-Reversal Recurrences"),
        Blocks(
            Paragraph(Text("All scalar values and the variables n and d are natural numbers; "
                + "N denotes their domain. Subtraction is natural subtraction, truncated at zero. "
                + "The operator digits_2(n) is Nat.digits 2 n: the little-endian binary digit "
                + "list, empty at zero. The operator ofDigits_2 evaluates a list in base two "
                + "with its first entry least significant. The operator dropLast removes the "
                + "last entry, reverse reverses a list, map(f,L) applies f entrywise to L, "
                + "append concatenates two lists, and [1] is the singleton list. The expression "
                + "d : N mapped to 1-d denotes the digit-complement function. The operator "
                + "count(c,L) counts entries equal to c in L. The operator log_2(n) is Nat.log "
                + "2 n, the floor of the base-two logarithm for positive n. Addition, "
                + "multiplication and powers are natural-number operations. The functions a "
                + "and complementRest are defined below; on positive inputs they represent "
                + "A059894 and A054429. A000120 counts one bits, and A023416 counts zero bits "
                + "in the canonical binary expansion of a positive number.")),
            Node("a", "Complement and reverse the lower bits", DefinitionFormula("a", true),
                "Remove the most significant bit, reverse and complement the remaining bits, "
                + "then append the most significant bit one. The definition is total on the "
                + "naturals; the recurrence and counting clauses below quantify over positive inputs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("complementRest", "Complement the lower bits without reversal",
                DefinitionFormula("complementRest", false),
                "This transformation complements every bit except the most significant one "
                + "and preserves the order of the lower bits.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A059894 recurrence and digit-count conjectures", ResultFormula(),
                "The entry cited in stephan2003a059894 attributes both conjectures to Ralf "
                + "Stephan. The binary digit lemmas for twice n and twice n plus one, together "
                + "with positional evaluation and digit-list length, give the two recurrences. "
                + "Reconstructing the transformed digit lists shows that reversal preserves "
                + "the one count and complementation turns the original zero count into the "
                + "one count below the retained leading one.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a059894-stephan-complement-reverse-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a059894-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula BaseTwoCall(string name, Formula argument) =>
        new Formula.Apply(new Formula.Subscript(Named(name), D(2)), [argument]);
    private static Formula Digits(Formula n) => BaseTwoCall("digits", n);
    private static Formula Log(Formula n) => BaseTwoCall("log", n);
    private static Formula Count(Formula digit, Formula list) => Call("count", digit, list);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(Formula variable) =>
        Seq(Forall, Sp, variable, Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula ForEveryPositive(Formula n, Formula conclusion) =>
        Seq(Bound(n), Parenthesized(Seq(D(0), Sp, Lt, Sp, n)), Sp, Implies, Sp,
            Parenthesized(conclusion));

    private static Formula DefinitionFormula(string name, bool reverse)
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula lowerBits = Call("dropLast", Digits(n));
        if (reverse)
        {
            lowerBits = Call("reverse", lowerBits);
        }
        Formula complement = Parenthesized(Seq(d, Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            D(1), Sp, Minus, Sp, d));
        Formula word = Call("append", Call("map", complement, lowerBits),
            Seq(OpenBracket, D(1), CloseBracket));
        return Disp(Seq(Bound(n), Equal(Call(name, n), BaseTwoCall("ofDigits", word))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula value = Call("a", n);
        Formula even = ForEveryPositive(n,
            Equal(Call("a", Mul(D(2), n)), Add(value, Power(D(2), Add(Log(n), D(1))))));
        Formula odd = ForEveryPositive(n,
            Equal(Call("a", Add(Mul(D(2), n), D(1))), Add(value, Power(D(2), Log(n)))));
        Formula ones = Count(D(1), Digits(value));
        Formula counts = ForEveryPositive(n, Conjunction(
            Equal(ones, Count(D(1), Digits(Call("complementRest", n)))),
            Equal(ones, Add(Count(D(0), Digits(n)), D(1)))));
        return Disp(Conjunction(Equal(Call("a", D(1)), D(1)),
            Conjunction(even, Conjunction(odd, counts))));
    }
}
