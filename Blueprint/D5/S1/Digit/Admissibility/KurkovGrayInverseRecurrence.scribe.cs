using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class KurkovGrayInverseRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kurkov2023a006068");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse Gray-code sequence OEIS A006068 satisfies Kurkov's highest-bit recurrence.",
        H("Kurkov's Inverse Gray-Code Recurrence"),
        Blocks(
            Paragraph(Text("All indices n and all values lie in the natural numbers N. "
                + "The function a is the inverse Gray-code sequence A006068; msb is the "
                + "most significant bit A053644 on positive inputs, and complementSecondBit "
                + "is A063946, which toggles the second bit from the left and fixes zero "
                + "and one. The imported frozen function gray from "
                + "GrayCodeBinaryRecurrenceClosedForm is gray(n)=xor(n,div(n,2)). "
                + "Here xor is bitwise exclusive-or, div is natural-number floor division, "
                + "and log(b,n) is Lean's natural-number floor logarithm Nat.log b n, "
                + "with log(2,0)=0. The operator ite(c,x,y) returns x when c holds and "
                + "y otherwise. Addition and powers are natural-number operations; "
                + "every subtraction is truncated at zero.")),
            Node("a", "Hanna's XOR-prefix definition", SequenceFormula(),
                "The definition of a is Hanna's XOR-prefix formula written as the "
                + "recursion n XOR a(n/2), terminating at zero. Repeated substitution "
                + "gives the XOR of n and its successive dyadic quotients. The inverse "
                + "property is proved below; it is not assumed in this definition.",
                DescribeRole.Definition),
            Node("msb", "The highest binary place", MsbFormula(),
                "For positive n, this is A053644(n). The displayed totalized formula "
                + "has msb(0)=1, whereas OEIS A053644(0)=0. The positive recurrence "
                + "uses msb only at positive arguments, including complementSecondBit(n).",
                DescribeRole.Definition),
            Node("complementSecondBit", "Complementing the second bit from the left",
                ComplementFormula(),
                "This is A063946, including its values zero at zero and one at one. "
                + "Both OEIS %F cases are proved and used inside result: for every "
                + "natural k, 2*2^k <= n < 3*2^k gives n+2^k, while "
                + "3*2^k <= n < 4*2^k gives n-2^k. Thus toggling the second bit "
                + "preserves the highest bit.", DescribeRole.Definition),
            Node("result", "The inverse property and Kurkov's recurrence", ResultFormula(),
                "The first clause is the OEIS %N property: a(n) is Gray-coded into n, "
                + "using the frozen gray. The second clause supplies a(0)=0. The last "
                + "clause proves Kurkov's September 9, 2023 conjecture for every positive "
                + "natural n: A053645 subtracts the highest bit from A063946(n), and "
                + "A053644(n) supplies the added highest bit. Live strong inductions "
                + "establish commutation with division by two, inverse identities, and "
                + "dyadic upper bounds; the two second-bit cases complete the recurrence.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a006068-kurkov-gray-inverse-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a006068-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n"), Equal(Call("a", n),
            Call("ite", Parenthesized(Equal(n, D(0))), D(0),
                Call("xor", n, Call("a", Call("div", n, D(2))))))));
    }

    private static Formula MsbFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n"), Equal(Call("msb", n),
            Power(D(2), Call("log", D(2), n)))));
    }

    private static Formula ComplementFormula()
    {
        Formula n = F.Id("n");
        Formula secondBit = Power(D(2), Parenthesized(Sub(Call("log", D(2), n), D(1))));
        return Disp(Seq(Bound("n"), Equal(Call("complementSecondBit", n),
            Call("ite", Parenthesized(Less(n, D(2))), n, Call("xor", n, secondBit)))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula complemented = Call("complementSecondBit", n);
        Formula inverse = Seq(Bound("n"), Equal(Call("gray", Call("a", n)), n));
        Formula zero = Equal(Call("a", D(0)), D(0));
        Formula recurrence = Seq(Bound("n"), Implication(Less(D(0), n),
            Equal(Call("a", n), Add(Call("a", Sub(complemented, Call("msb", complemented))),
                Call("msb", n)))));
        return Disp(Conjunction(inverse, Conjunction(zero, recurrence)));
    }
}
