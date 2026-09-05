using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class ThueMorseReducedAbelianOddDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-start reduced abelian complexity of the Thue-Morse word obeys the "
            + "odd-index recurrence and equals three at every power of two plus one.",
        H("Odd Reduced Abelian Complexity of the Thue-Morse Word"),
        Blocks(
            Paragraph(Text(
                "The word is indexed from zero: thueMorse(s) is the parity of the number of "
                    + "one-bits of s, and therefore equals the paper's one-based letter "
                    + "t_(s+1). Campbell, Currie, and Rampersad stated the odd-index equality "
                    + "as an apparent pattern in arXiv:2509.16034v1, Section 3, without a proof. "
                    + "Every result below is derived in this repository; the paper is context, "
                    + "not a source of any assumed theorem.")),
            Describe.Lean(
                DescribeId.Create("zero-indexed-thue-morse-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse"),
                H("The zero-indexed Thue-Morse word"),
                StatementSource.FromAuthor(ThueMorseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nat.binaryRec starts at false and updates the accumulated parity by "
                        + "Boolean inequality with the next low binary digit. Thus this is "
                        + "exactly binary popcount parity, not a sampled finite prefix. "
                        + "The middle argument is ignored, as in Lean's anonymous binder."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("run-reduced-parikh-vector"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedParikh"),
                H("The Parikh vector after run reduction"),
                StatementSource.FromAuthor(ReducedParikhFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here runs(length,start) counts maximal constant runs in the indicated "
                        + "factor. Run reduction is alternating, so a false initial letter gives "
                        + "r-floor(r/2) false letters and floor(r/2) true letters; a true initial "
                        + "letter reverses those coordinates. The displayed natDiv operation is "
                        + "natural-number floor division, exactly Lean's Nat.div."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-abelian-equivalence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd."
                        + "ReducedAbelianEquivalent"),
                H("Reduced abelian equivalence at a common length"),
                StatementSource.FromAuthor(ReducedAbelianEquivalentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two factors of the same supplied length are equivalent precisely when the "
                        + "Parikh vectors of their run reductions are equal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-reduced-abelian-code"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianCode"),
                H("The canonical code for a reduced abelian class"),
                StatementSource.FromAuthor(ReducedAbelianCodeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The run count is always retained. For even run count the two initial "
                        + "letters have the same reduced Parikh vector, so the Boolean coordinate "
                        + "is canonically false; for odd run count it records the actual first "
                        + "letter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-parikh-equality-iff-code-equality"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd."
                        + "reducedAbelianEquivalent_iff_code_eq"),
                H("Reduced Parikh equality is exactly code equality"),
                StatementSource.FromAuthor(ReducedAbelianEquivalentIffCodeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate sum recovers the run count. With equal run counts, the two "
                        + "alternating Parikh vectors agree automatically in the even case and "
                        + "agree exactly when their initial letters agree in the odd case. This "
                        + "is the preregistered class-code equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-start-reduced-abelian-classes"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd."
                        + "reducedAbelianClasses"),
                H("Reduced abelian classes over all natural starts"),
                StatementSource.FromAuthor(ReducedAbelianClassesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite ambient square contains coordinate pairs from zero through "
                        + "length. Filtering it by existence of an arbitrary natural start "
                        + "retains exactly every reduced Parikh vector that occurs anywhere in "
                        + "the infinite word. No prefix bound or sampling hypothesis appears."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced-abelian-complexity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.R"),
                H("Reduced abelian complexity"),
                StatementSource.FromAuthor(RFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "R(length) is the cardinality of the all-start finite class set, matching "
                        + "the source definition rather than the number seen in a chosen prefix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-index-reduced-abelian-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd."
                        + "reducedAbelianComplexity_odd"),
                H("Odd indices reflect to half length"),
                StatementSource.FromAuthor(OddRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The transition identities transition(2q)=1 and "
                            + "transition(2q+1)=1-transition(q) prove, for starts of either "
                            + "parity, runs(2n+1,p)=2n+2-runs(n+1,floor(p/2)). The reflection "
                            + "preserves run-count parity.")),
                    Paragraph(Text(
                        "For every factor, the explicit start "
                            + "2^(start+length+1)+start gives a factor with the same run count "
                            + "and complementary initial letter, by the high-power shift identity "
                            + "thueMorse(2^k+x)=not thueMorse(x), for x<2^k. The constructed "
                            + "shift satisfies this bound. This supplies the odd-start surjectivity case.")),
                    Paragraph(Text(
                        "Reflection is therefore a bijection on the canonical codes. The code "
                            + "equivalence transfers that bijection to reduced Parikh classes, "
                            + "and taking finite cardinalities proves the equality for every n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-of-two-plus-one-complexity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd."
                        + "reducedAbelianComplexity_two_pow_add_one"),
                H("Power of two plus one has complexity three"),
                StatementSource.FromAuthor(TwoPowAddOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A kernel-decided certificate constructs and exhausts the three length-two "
                        + "classes (1,0), (0,1), and (1,1). Induction then rewrites each successor "
                        + "power through the odd recurrence. No native_decide step is used."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ThueMorseFormula()
    {
        Formula bit = F.Id("bit");
        Formula parity = F.Id("parity");
        Formula step = Seq(
            Parenthesized(Seq(bit, Comma, Sp, new Formula.Placeholder(), Comma, Sp, parity)),
            Sp, Mapsto, Sp, bit, Sp, Neq, Sp, parity);
        return Disp(Seq(
            F.Id("thueMorse"), Colon, Sp, Naturals(), Sp, To, Sp, BoolType(), Comma, Sp,
            F.Id("thueMorse"), Sp, Eq, Sp,
            Apply(Seq(F.Id("Nat"), Dot, F.Id("binaryRec")), F.Id("false"), step), Dot));
    }

    private static Formula RunCountFormula(Formula length, Formula start)
    {
        Formula i = F.Id("i");
        Formula at = Seq(start, Sp, Plus, Sp, i);
        Formula step = Call("if", Seq(Call("thueMorse", at), Sp, Eq, Sp,
            Call("thueMorse", Seq(at, Sp, Plus, Sp, D(1)))), D(0), D(1));
        Formula range = Apply(Seq(F.Id("Finset"), Dot, F.Id("range")),
            Seq(length, Sp, Minus, Sp, D(1)));
        Formula sum = Apply(Seq(F.Id("Finset"), Dot, F.Id("sum")), range,
            Seq(i, Sp, Mapsto, Sp, step));
        return Call("if", Seq(length, Sp, Eq, Sp, D(0)), D(0),
            Seq(D(1), Sp, Plus, Sp, sum));
    }

    private static Formula ReducedParikhFormula()
    {
        Formula length = F.Id("length");
        Formula start = F.Id("start");
        Formula runCount = RunCountFormula(length, start);
        Formula half = Call("natDiv", runCount, D(2));
        Formula otherHalf = Seq(runCount, Sp, Minus, Sp, half);
        Formula trueCase = Pair(half, otherHalf);
        Formula falseCase = Pair(otherHalf, half);
        return Disp(Seq(
            Forall, Sp, length, Comma, Sp, start, InMacro, Naturals(), Comma, Sp,
            Call("reducedParikh", length, start), Sp, Eq, Sp,
            Call("if", Call("thueMorse", start), trueCase, falseCase), Dot));
    }

    private static Formula ReducedAbelianEquivalentFormula()
    {
        Formula length = F.Id("length");
        Formula start1 = F.Id("start1");
        Formula start2 = F.Id("start2");
        return Disp(Seq(
            Forall, Sp, length, Comma, Sp, start1, Comma, Sp, start2,
            InMacro, Naturals(), Comma, Sp,
            Call("ReducedAbelianEquivalent", length, start1, start2), Sp, Iff, Sp,
            Call("reducedParikh", length, start1), Sp, Eq, Sp,
            Call("reducedParikh", length, start2), Dot));
    }

    private static Formula ReducedAbelianCodeFormula()
    {
        Formula length = F.Id("length");
        Formula start = F.Id("start");
        Formula runCount = RunCountFormula(length, start);
        Formula letter = Call(
            "if", Call("Odd", runCount), Call("thueMorse", start), F.Id("false"));
        return Disp(Seq(
            Forall, Sp, length, Comma, Sp, start, InMacro, Naturals(), Comma, Sp,
            Call("reducedAbelianCode", length, start), Sp, Eq, Sp,
            Pair(runCount, letter), Dot));
    }

    private static Formula ReducedAbelianEquivalentIffCodeFormula()
    {
        Formula length = F.Id("length");
        Formula start1 = F.Id("start1");
        Formula start2 = F.Id("start2");
        return Disp(Seq(
            Forall, Sp, length, Comma, Sp, start1, Comma, Sp, start2,
            InMacro, Naturals(), Comma, Sp,
            Call("ReducedAbelianEquivalent", length, start1, start2), Sp, Iff, Sp,
            Call("reducedAbelianCode", length, start1), Sp, Eq, Sp,
            Call("reducedAbelianCode", length, start2), Dot));
    }

    private static Formula ReducedAbelianClassesFormula()
    {
        Formula length = F.Id("length");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula start = F.Id("start");
        Formula pair = Pair(first, second);
        Formula bounded = Seq(
            first, Sp, Leq, Sp, length, Sp, Land, Sp,
            second, Sp, Leq, Sp, length);
        Formula witnessed = Seq(
            Exists, Sp, start, InMacro, Naturals(), Comma, Sp,
            Call("reducedParikh", length, start), Sp, Eq, Sp, pair);
        return Disp(Seq(
            Forall, Sp, length, InMacro, Naturals(), Comma, Sp,
            Call("reducedAbelianClasses", length), Sp, Eq, Sp,
            OpenBrace, pair, Sp, Mid, Sp,
            Parenthesized(bounded), Sp, Land, Sp, Parenthesized(witnessed),
            CloseBrace, Dot));
    }

    private static Formula RFormula()
    {
        Formula length = F.Id("length");
        return Disp(Seq(
            Forall, Sp, length, InMacro, Naturals(), Comma, Sp,
            Call("R", length), Sp, Eq, Sp,
            Call("card", Call("reducedAbelianClasses", length)), Dot));
    }

    private static Formula OddRecurrenceFormula()
    {
        Formula n = F.Id("n");
        Formula oddLength = Seq(D(2), Sp, Times, Sp, n, Sp, Plus, Sp, D(1));
        Formula shortLength = Seq(n, Sp, Plus, Sp, D(1));
        return Disp(Seq(
            Forall, Sp, n, InMacro, Naturals(), Comma, Sp,
            Call("R", oddLength), Sp, Eq, Sp, Call("R", shortLength), Dot));
    }

    private static Formula TwoPowAddOneFormula()
    {
        Formula k = F.Id("k");
        Formula length = Seq(Power(D(2), k), Sp, Plus, Sp, D(1));
        return Disp(Seq(
            Forall, Sp, k, InMacro, Naturals(), Comma, Sp,
            Call("R", length), Sp, Eq, Sp, D(3), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(function, Parenthesized(Seq([.. items])));
    }

    private static Formula Pair(Formula first, Formula second) =>
        Parenthesized(Seq(first, Comma, Sp, second));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula BoolType() => Seq(Operatorname, Grp(F.Id("Bool")));
}
