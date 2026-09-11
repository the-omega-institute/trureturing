using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class SecantNumberPurePeriodRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/bala2023a000364");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euler secant numbers refute pure periodicity with period dividing phi(27).",
        H("A Counterexample to Pure Periodicity of the Secant Numbers"),
        Blocks(
            Paragraph(Text("The comment recorded in bala2023a000364 conjectures pure periodicity "
                + "of the sequence starting at index 1, with period dividing phi(k), for every "
                + "integer modulus k. Here k is 27. The symbols a and b denote the integer "
                + "sequence and its independently defined recurrence in ZMod(27). The function "
                + "red denotes the canonical map from the integers to ZMod(27), choose denotes "
                + "the natural binomial coefficient, and phi denotes Euler's totient. All "
                + "indices are natural numbers; subtraction in an index is natural subtraction. "
                + "The sum over j in Fin(n+1) uses the natural value of j in every summand. "
                + "Numerals, signs, products and sums in each recurrence are interpreted in "
                + "the codomain of that sequence.")),
            Node("a", "The integer secant recurrence", DefinitionFormula("a", Integers()),
                "The integer sequence a has constant value a(0)=1 and obeys the recurrence "
                + "in bala2023a000364 with its summation index shifted by one.", DescribeRole.Definition),
            Node("b", "The recurrence modulo 27", DefinitionFormula("b", ResidueRing()),
                "The sequence b is defined by the same recurrence directly in ZMod(27).",
                DescribeRole.Definition),
            Node("a_recurrence", "The defining recurrence holds", Disp(Recurrence("a")),
                "Unfolding a gives both the initial condition and the recurrence."),
            Node("a_unique", "The recurrence determines a uniquely", UniquenessFormula(),
                "Strong induction compares c and a at every index. Each term on the "
                + "right uses a strictly smaller index, so equality propagates to the next coefficient."),
            Node("initial_values", "Agreement with the initial published values", InitialFormula(),
                "The defining integer recurrence gives the first four DATA values in bala2023a000364."),
            Node("reduction", "Reduction commutes with the recurrence",
                Disp(All("n", Naturals(), Equal(Call("red", Call("a", V("n"))), Call("b", V("n"))))),
                "Strong induction moves the integer cast through the finite sum, powers and "
                + "products, then identifies every smaller coefficient with b."),
            Node("residue_one", "The first positive coefficient modulo 27",
                Disp(Equal(Call("red", Call("a", D(1))), D(1))),
                "Reduction of the first positive coefficient gives 1 in ZMod(27)."),
            Node("residue_nineteen", "The nineteenth coefficient modulo 27",
                Disp(Equal(Call("red", Call("a", D(1, 9))), D(1, 0))),
                "Successive evaluations of the reduced recurrence give b(19)=10. "
                + "The reduction theorem transfers this certificate to a."),
            Node("balaConjecture", "The conjecture at modulus 27",
                Disp(Seq(Call("balaConjecture"), Sp, Iff, Sp, Parenthesized(Conjecture()))),
                "The proposition balaConjecture says that the sequence from index 1 has a "
                + "positive period d dividing phi(27).", DescribeRole.Definition),
            Node("bala_conjecture_false", "Pure periodicity fails at modulus 27",
                Disp(Seq(Neg, Sp, Parenthesized(Call("balaConjecture")))),
                "Any period d dividing phi(27)=18 would make 18 a period, by the theorem "
                + "that a natural multiple of a period is a period. This would equate "
                + "red(a(1))=1 with red(a(19))=10 in ZMod(27), a contradiction. "
                + "This refutes the word purely in the conjecture; it makes no claim "
                + "about eventual periodicity or about the stated odd-prime theorem.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a000364-secant-number-pure-period-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("secant-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula ResidueRing() => Call("ZMod", D(2, 7));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Subtract(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Cdot, Sp, Parenthesized(y));
    private static Formula And(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Land, Sp, Parenthesized(y));
    private static Formula Implication(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula RecurrenceStep(string name)
    {
        var n = V("n");
        var j = V("j");
        var sign = new Formula.Power(Parenthesized(Seq(Minus, D(1))), Add(j, D(2)));
        var coefficient = Call("choose", Mul(D(2), Add(n, D(1))), Mul(D(2), Add(j, D(1))));
        var sum = Seq(new Formula.Subscript(F.Sum,
            Seq(j, Sp, InMacro, Sp, Call("Fin", Add(n, D(1))))), Sp,
            Parenthesized(Mul(Mul(sign, coefficient), Call(name, Subtract(n, j)))));
        return All("n", Naturals(), Equal(Call(name, Add(n, D(1))), sum));
    }
    private static Formula Recurrence(string name) =>
        And(Equal(Call(name, D(0)), D(1)), RecurrenceStep(name));
    private static Formula DefinitionFormula(string name, Formula codomain) => Disp(new Formula.Aligned([
        Seq(V(name), Colon, Sp, Naturals(), Sp, To, Sp, codomain), Recurrence(name)
    ]));
    private static Formula UniquenessFormula() => Disp(All("c",
        Seq(Naturals(), Sp, To, Sp, Integers()),
        Implication(Equal(Call("c", D(0)), D(1)),
            Implication(RecurrenceStep("c"), Equal(V("c"), V("a"))))));
    private static Formula InitialFormula() => Disp(And(Equal(Call("a", D(0)), D(1)),
        And(Equal(Call("a", D(1)), D(1)), And(Equal(Call("a", D(2)), D(5)),
            Equal(Call("a", D(3)), D(6, 1))))));
    private static Formula Conjecture() => Seq(Exists, Sp, V("d"), Colon, Sp, Naturals(), Comma, Sp,
        Parenthesized(And(Seq(D(0), Sp, Lt, Sp, V("d")),
            And(Seq(V("d"), Sp, Mid, Sp, Call("phi", D(2, 7))),
                All("n", Naturals(), Implication(Seq(D(1), Sp, Le, Sp, V("n")),
                    Equal(Call("red", Call("a", Add(V("n"), V("d")))),
                        Call("red", Call("a", V("n"))))))))));
}
