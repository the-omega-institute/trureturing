using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciIntegerIntervalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual integer weighted sum uniquely represents the initial k-bonacci interval.",
        H("Integer intervals represented by run-avoiding words"),
        Blocks(
            Paragraph(Text(
                "Fix a natural order k at least two. Write G(j)=dbonacci k (j+2). "
                + "For j<k the weight is 2^j; for j at least k it is the sum of "
                + "the preceding k weights. These are the initial-power and recurrence "
                + "laws of DBonacci.Names. A word has exactly n Boolean coordinates. "
                + "Coordinate zero is the least significant digit, and a true bit "
                + "contributes its integer weight while a false bit contributes zero.")),
            Describe.Lean(
                DescribeId.Create("integer-value"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval.integerValue"),
                H("The specified integer weighted sum"),
                StatementSource.FromAuthor(Disp(ValueFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here val(i) is the natural coordinate of a finite index, ofNat "
                    + "is the canonical embedding into the integers, and ite selects "
                    + "its first value on a true Boolean. Thus the value is the exact "
                    + "sum of bit times integer weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-value-interval-bijection"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval."
                    + "integer_value_interval_bijection"),
                H("Every length, every order, and the actual value map"),
                StatementSource.FromAuthor(Disp(BijectionFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "TrueBlock(w,s,k) requires s+k at most n and every bit in "
                        + "[s,s+k) to be true. Ico denotes a lower-closed, upper-open "
                        + "integer interval, so the target is precisely the integers "
                        + "from zero through G(n)-1. BijOn includes membership of every "
                        + "value in that interval, injectivity on all literal legal "
                        + "words, and surjectivity onto every integer in the interval.")),
                    Paragraph(Text(
                        "Read a word from its highest bit while keeping the scanner's "
                        + "remaining true-bit budget. A zero resets the budget and "
                        + "leaves the tail value unchanged. A one consumes one unit of "
                        + "budget and adds G(q), where q is the tail length. The "
                        + "existing bounded-run split separates these cases. Induction "
                        + "on length proves that each tail's actual weighted sum is "
                        + "below the cardinality of its budget layer and is injective. "
                        + "The zero branch is below G(q); the one branch is at least "
                        + "G(q). Within either branch, tail injectivity applies. The "
                        + "existing layer count then makes this bounded integer map "
                        + "surjective.")),
                    Paragraph(Text(
                        "For n at least k, iterate this split to the first zero. "
                        + "Every legal high-first word has a unique prefix of j ones "
                        + "followed by zero, with 0 at most j and j<k, and a legal tail "
                        + "of length n-j-1. Put A(0)=0 and "
                        + "A(j)=G(n-1)+G(n-2)+...+G(n-j). The prefix contributes "
                        + "exactly A(j). The tail bijection therefore gives the whole "
                        + "group exactly the interval [A(j),A(j)+G(n-j-1)), which is "
                        + "[A(j),A(j+1)). The endpoints are adjacent; positivity of "
                        + "the weights makes the groups disjoint. The recurrence gives "
                        + "A(k)=G(n), so these groups exhaust the target interval. "
                        + "Locating the group of a target value, subtracting its "
                        + "prefix contribution, and recurring on the shorter tail "
                        + "gives the fixed-length encoding procedure.")),
                    Paragraph(Text(
                        "For n<k every word is legal and all used weights are powers "
                        + "of two. The same induction includes this binary case. "
                        + "At n=0 there is one empty word, its sum is zero, and G(0)=1. "
                        + "Reversing finite indices changes high-first printing into "
                        + "the least-significant-first coordinates of the formula. "
                        + "A forbidden block beginning at s becomes the block beginning "
                        + "at n-(s+k), including a block ending at the final bit. "
                        + "The scanner and literal block condition agree at every "
                        + "length: the closed-word equivalence supplies n at least k, "
                        + "and both conditions are automatic at shorter lengths. "
                        + "Finally the natural sum embeds exactly into the nonnegative "
                        + "integers; every nonnegative target integer is recovered "
                        + "from its toNat representative."))),
                DescribeRole.Theorem))));

    private static Formula ValueFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var w = F.Id("w");
        var i = F.Id("i");
        var weight = Fn("ofNat", Fn("dbonacci", k, Seq(Fn("val", i), Plus, D(2))));
        var sum = Seq(Sum, Underscore, Grp(i, Colon, Sp, Fn("Fin", n)), Sp,
            Fn("ite", new Formula.Apply(w, [i]), weight, D(0)));
        return All(Seq(k, Comma, n), Nat, All(w, Word(n),
            Rel(Fn("integerValue", k, w), Eq, sum)));
    }

    private static Formula BijectionFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var w = F.Id("w");
        var s = F.Id("s");
        var legal = Seq(OpenBrace, w, Colon, Sp, Word(n), Sp, Mid, Sp,
            All(s, Nat, Seq(Neg, Sp, Fn("TrueBlock", w, s, k))), CloseBrace);
        var endpoint = Fn("ofNat", Fn("dbonacci", k, Seq(n, Plus, D(2))));
        return All(Seq(k, Comma, n), Nat, Seq(
            D(2), Leq, Sp, k, Sp, Implies, Sp,
            Fn("BijOn", Fn("integerValue", k), legal, Fn("Ico", D(0), endpoint))));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula n) => Seq(Fn("Fin", n), Sp, To, Sp, Fn("Bool"));
    private static Formula Fn(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(left, Sp, relation, Sp, right);
    private static Formula All(Formula variables, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, variables, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
}
