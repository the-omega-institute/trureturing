using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class AyadBouchennaReverseMultipleDivisorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/AyadBouchennaReverseMultipleDivisors.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/ayad2025reversemultiples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Divisors of B squared minus one are exactly the positive divisors of all their reversed base-B multiples.",
        H("Divisors of All Reversed Multiples"),
        Blocks(
            Node("reverseBase", "Reversal in a base", ReverseFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Blocks(
                    Paragraph(Text("Ayad and Bouchenna, section 4.1, p. 8: “For every positive integer "),
                        Math(Equal(F.Id("m"), SourceDigits(false))),
                        Text(", we call the integer "), Math(Equal(StarB("m"), SourceDigits(true))),
                        Text(". the reverse of "), Math(F.Id("m")), Text(" in base "),
                        Math(F.Id("B")), Text("”")),
                    Paragraph(Text("Here digits(B,m) is Nat.digits B m, in least-significant-first order; "
                        + "reverse is List.reverse and ofDigits is Nat.ofDigits. Reversing and evaluating "
                        + "therefore gives the displayed source expression. Trailing zeros of m become "
                        + "leading zeros of its reversal and contribute zero. The definition is total "
                        + "on natural B and m; the theorem restricts B to at least two and m to positive multiples.")))),
            Node("HasReverseMultipleProperty", "Divisibility of every reversed multiple", PropertyFormula(),
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition,
                Blocks(
                    Paragraph(Text("Ayad and Bouchenna, section 4.1, p. 8: “A positive integer "),
                        Math(F.Id("n")), Text(" is said to have the property "), Math(StarB("P")),
                        Text(" if "), Math(F.Id("n")), Text(" divides "), Math(StarB("m")),
                        Text(" for any positive multiple "), Math(F.Id("m")), Text(" of "),
                        Math(F.Id("n")), Text(", that is, if for every positive integer "),
                        Math(F.Id("m")), Text(", if "), Math(F.Id("n")), Text(" divides "),
                        Math(F.Id("m")), Text(", then "), Math(F.Id("n")), Text(" divides "),
                        Math(StarB("m")), Text(".”")),
                    Paragraph(Text("The predicate quantifies over all natural m with 0 < m and n dividing m. "
                        + "Its parameters B and n are natural numbers; positivity of n and B ≥ 2 are "
                        + "explicit hypotheses of the characterization.")))),
            Node("result", "The characterization in every base", ResultFormula(),
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                Blocks(
                    Paragraph(Text("Ayad and Bouchenna, Problem 1, p. 9: “Let "),
                        Math(new Formula.Relation(F.Id("B"), FormulaRelationOperator.GreaterThanOrEqual, D(2))),
                        Text(" be any number base. Are the divisors of "), Math(SquareMinusOne()),
                        Text(" the only positive integers satisfying the property "), Math(StarB("P")),
                        Text(" ?”")),
                    Paragraph(Text("The answer is yes for every natural base B ≥ 2 and every positive natural n. "
                        + "The implication from divisibility by B² − 1 is Proposition 5 on p. 8. "
                        + "The converse follows by first forcing n to be coprime to B using a multiple "
                        + "with leading digit one. If B² is not one modulo n, the multiplicative order "
                        + "T of B is at least two. Sparse digit lists have ones at positions "
                        + "0, 1, T, …, (c+1)T. "
                        + "Their forward and reversed residues force B² = 1 modulo n. "
                        + "The vertical bars in the statement denote divisibility; B² − 1 is natural "
                        + "subtraction, agreeing with integer subtraction under B ≥ 2.")))))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, DescribeRole role, BlockSequence prose) =>
        Describe.Lean(DescribeId.Create("ayad-reverse-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, prose, role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula SquareMinusOne() =>
        new Formula.Binary(new Formula.Power(F.Id("B"), D(2)), FormulaBinaryOperator.Subtract, D(1));
    private static Formula StarB(string name) =>
        Seq(F.Id(name), Caret, Grp(Star), Underscore, Grp(F.Id("B")));
    private static Formula Digit(Formula index) => new Formula.Subscript(F.Id("a"), index);
    private static Formula SourceDigits(bool reversed) => reversed
        ? Seq(Digit(D(0)), new Formula.Power(F.Id("B"), F.Id("k")), Plus,
            Digit(D(1)), new Formula.Power(F.Id("B"),
                new Formula.Binary(F.Id("k"), FormulaBinaryOperator.Subtract, D(1))),
            Plus, Cdot, Cdot, Cdot, Plus, Digit(F.Id("k")))
        : Seq(Digit(F.Id("k")), new Formula.Power(F.Id("B"), F.Id("k")),
            Plus, Cdot, Cdot, Cdot, Plus, Digit(D(1)), F.Id("B"), Plus, Digit(D(0)));

    private static Formula ReverseFormula()
    {
        var digits = Call("digits", F.Id("B"), F.Id("m"));
        var value = Call("ofDigits", F.Id("B"), Call("reverse", digits));
        return Disp(All("B", All("m", Equal(Call("reverseBase", F.Id("B"), F.Id("m")), value))));
    }

    private static Formula PropertyFormula()
    {
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("m"));
        var reversed = Divides(F.Id("n"), Call("reverseBase", F.Id("B"), F.Id("m")));
        var property = All("m", Implies(positive, Implies(Divides(F.Id("n"), F.Id("m")), reversed)));
        return Disp(All("B", All("n", Equal(
            Call("HasReverseMultipleProperty", F.Id("B"), F.Id("n")), Parenthesized(property)))));
    }

    private static Formula ResultFormula() => Disp(All("B", Implies(
        new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, F.Id("B")),
        All("n", Implies(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("n")),
            new Formula.Logic(Call("HasReverseMultipleProperty", F.Id("B"), F.Id("n")),
                FormulaLogicOperator.Iff, Divides(F.Id("n"), SquareMinusOne())))))));
}
