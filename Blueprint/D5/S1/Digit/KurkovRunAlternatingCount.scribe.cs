using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class KurkovRunAlternatingCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/KurkovRunAlternatingCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/sloane2014a239907");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating overlapping binary one-block counts give Kurkov's A329320 identity.",
        H("Kurkov's Alternating Binary Run Count"),
        Blocks(
            Paragraph(Text(
                "The symbols n, k, i, and j are natural numbers, including zero. "
                    + "The operator size(n) is the length of the binary expansion, "
                    + "equal to floor(log_2(n))+1 for positive n and zero at n=0. "
                    + "The Boolean testBit(n,i) is true exactly when bit i is one, "
                    + "with the least significant bit at i=0 and zero bits beyond size(n). "
                    + "The function cn(n,k) counts occurrences of the block of k ones; "
                    + "overlapping occurrences have distinct starting indices and all count. "
                    + "The operator v_2(m) is the exponent of two dividing positive m, "
                    + "and Odd(r) means r=2q+1 for some natural q. The function b(n) "
                    + "counts suffixes whose shifted value plus one has odd v_2. "
                    + "Vertical bars denote finite-set cardinality. The operator div "
                    + "is natural-number floor division, and (x:Z) is the natural-to-integer "
                    + "coercion. Indices, valuations, and exponents are natural; the "
                    + "alternating sum and both subtractions in the theorem are integer "
                    + "operations. Only Kurkov's October 13, 2021 formula in A239907 "
                    + "is settled here, using the cited valuation interpretation of A329320.")),
            Node("cn", "Overlapping occurrences of a block of ones", CnFormula(),
                "For positive k the predicate tests every bit in the block beginning at i. "
                    + "Reversing the binary word preserves occurrences of a block of ones. "
                    + "For example cn(7,2)=2, which gives the overlapping reading required "
                    + "by A239907. The value cn(n,0)=size(n) is a totalization excluded "
                    + "from the alternating sum.",
                DescribeRole.Definition),
            Node("b", "A329320 in valuation coordinates", BFormula(),
                "For positive m the cited characterization is "
                    + "1-A035263(m)=[v_2(m) odd], where brackets denote the zero-or-one "
                    + "indicator. Thus this cardinality is the sum in the NAME of A329320. "
                    + "Every argument div(n,2^i)+1 is positive. The range is empty at zero, "
                    + "so b(0)=0. The morphic definition of A035263 is not separately "
                    + "formalized by this statement.",
                DescribeRole.Definition),
            Node("result", "Kurkov's identity", ResultFormula(),
                "A block of k ones starting at i exists exactly when "
                    + "2^k divides div(n,2^i)+1, equivalently when k is at most its v_2. "
                    + "This valuation is at most size(n) for each counted start. "
                    + "Interchanging the two finite sums reduces the alternating count "
                    + "at that start to one for an odd valuation and zero for an even "
                    + "valuation. Their sum is b(n). Both ranges are empty at n=0, "
                    + "and the equality then reads 0=0.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a239907-kurkov-run-alternating-count"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a239907-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula ValuationTwo(Formula value) =>
        new Formula.Apply(new Formula.Subscript(Named("v"), D(2)), [value]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula IntegerCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Integers()));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula.BoundVariable Bound(string name) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals());
    private static Formula Universal(Formula.BoundVariable[] variables, Formula body) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body));

    private static Formula CountStarts(Formula n, Formula i, Formula predicate) =>
        new Formula.Absolute(Seq(
            Left, OpenBrace,
            new Formula.Relation(i, FormulaRelationOperator.MemberOf, Naturals()),
            Sp, Mid, Sp,
            new Formula.Logic(
                Parenthesized(LessThan(i, Call("size", n))),
                FormulaLogicOperator.And, Parenthesized(predicate)),
            Right, CloseBrace));

    private static Formula CnFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula block = new Formula.BindMany(
            FormulaQuantifier.ForAll, [Bound("j")],
            new Formula.Logic(
                Parenthesized(LessThan(j, k)), FormulaLogicOperator.Implies,
                Parenthesized(Equal(Call("testBit", n, Add(i, j)), Named("true")))));
        return Universal([Bound("n"), Bound("k")],
            Equal(Call("cn", n, k), CountStarts(n, i, block)));
    }

    private static Formula BFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula shifted = Call("div", n, new Formula.Power(D(2), i));
        Formula oddValuation = Call("Odd", ValuationTwo(Add(shifted, D(1))));
        return Universal([Bound("n")], Equal(Call("b", n), CountStarts(n, i, oddValuation)));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula sign = new Formula.Power(
            Parenthesized(Seq(new Formula.Negate(D(1)), Colon, Sp, Integers())), Add(k, D(1)));
        Formula sum = Seq(F.Sum, Underscore, Grp(k, Sp, Eq, Sp, D(1)),
            Caret, Grp(Call("size", n)), Sp, Multiply(sign, IntegerCast(Call("cn", n, k))));
        return Universal([Bound("n")],
            Equal(Subtract(IntegerCast(n), sum), Subtract(IntegerCast(n), IntegerCast(Call("b", n)))));
    }
}
