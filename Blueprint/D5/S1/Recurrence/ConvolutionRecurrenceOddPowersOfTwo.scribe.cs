using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class ConvolutionRecurrenceOddPowersOfTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection of a convolution sum modulo two proves the parity conjecture for OEIS A397588.",
        H("Convolution Recurrence Odd Exactly at Powers of Two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("convolution-parity-sequence"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a"),
                H("The natural-number convolution sequence"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition uses the recurrence of OEIS A397588, Paul D. Hanna, "
                        + "July 3, 2026; the symmetric formula is credited there to Seiichi Manyama. "
                        + "The operator ite selects its second argument when its first argument "
                        + "holds, and its third otherwise. Icc is the inclusive natural-number "
                        + "interval; attach retains its membership proofs, and val forgets them. "
                        + "All subtractions in indices are natural subtraction, truncated at zero. "
                        + "Well-founded recursion uses strictly smaller indices in the sum. "
                        + "At zero the sum is empty, giving a(0)=0 outside the source domain. "
                        + "The standard well-founded fix combinator implements this recursive "
                        + "equation, using the membership bounds to justify both recursive calls."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("convolution-parity-initial-value"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_one"),
                H("Initial value"),
                StatementSource.FromAuthor(Disp(Equal(A(D(1)), D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This unfolds the initial-value clause of the definition and supplies "
                        + "the base case of the parity characterization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-parity-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_recurrence"),
                H("The source recurrence"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Removing only the membership-proof attachment exposes the exact source "
                        + "sum from one through n-1 for every n greater than one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-parity-pairing"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.convolution_pairing"),
                H("Off-diagonal cancellation"),
                StatementSource.FromAuthor(PairingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Erase the midpoint m. Reflection k to 2m-k preserves the remaining interval, "
                        + "has no fixed point there, and is an involution. Each paired product "
                        + "occurs twice and cancels in ZMod(2). Restoring the midpoint leaves its "
                        + "square. This is the general pairing witness used in the halving theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-parity-halving-via-square"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_halving_via_square"),
                H("Even-index reduction through the midpoint square"),
                StatementSource.FromAuthor(HalvingViaSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive m, the recurrence and convolution pairing first identify "
                        + "the cast of a(2m) with the square of the cast of a(m). The second conjunct "
                        + "records that every element of ZMod(2) equals its square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-parity-halving"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_halving"),
                H("Halving an even index"),
                StatementSource.FromAuthor(HalvingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here and below cast(x,ZMod(2)) denotes the natural-number cast into the "
                        + "ring of integers modulo two. The recurrence factor 2m+1 casts to one. "
                        + "Pairing leaves the square of the midpoint value, and every element "
                        + "of ZMod(2) equals its square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-parity-odd-index"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_odd_index_zero"),
                H("Odd indices greater than one"),
                StatementSource.FromAuthor(OddIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For odd n greater than one, the factor n+1 is even, so the recurrence "
                        + "casts to zero. The parity characterization consumes this companion "
                        + "in its odd-index branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-parity-power-two-characterization"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.a_odd_iff_power_two"),
                H("Odd values occur exactly at powers of two"),
                StatementSource.FromAuthor(CharacterizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "OEIS A397588 states this as a conjecture in its July 3, 2026 entry; "
                        + "the proof is derived here. Strong induction handles n=1 directly, "
                        + "halves positive even indices, and excludes odd indices greater than one. "
                        + "The bridge is that the natural cast into ZMod(2) equals one exactly "
                        + "when the natural number is Odd. The existential exponent is a natural "
                        + "number, hence nonnegative. Both directions hold for every positive index."))),
                DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula value = Call("val", k);
        Formula sum = FiniteSum(k, Call("attach", Interval(n)),
            Product(A(value), A(Difference(n, value))));
        return Disp(new Formula.Aligned([
            Seq(F.Id("a"), Colon, Sp, Naturals(), Sp, To, Sp, Naturals(), Comma),
            Seq(Bound(n), Equal(A(n), Call("ite", Equal(n, D(1)), D(1),
                Product(Parenthesized(Add(n, D(1))), Parenthesized(sum))))),
        ]));
    }

    private static Formula RecurrenceFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound(n), Parenthesized(Less(D(1), n)), Sp, Rightarrow, Sp,
            Equal(A(n), Product(Parenthesized(Add(n, D(1))),
                Parenthesized(Convolution("a", n))))));
    }

    private static Formula PairingFormula()
    {
        Formula f = F.Id("f");
        Formula m = F.Id("m");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, f, Colon, Sp, Parenthesized(Seq(Naturals(), Sp, To, Sp, ModTwo())),
                Comma, Sp, Bound(m)),
            Seq(Parenthesized(AtLeastOne(m)), Sp, Rightarrow, Sp,
                Equal(Convolution("f", Product(D(2), m)), new Formula.Power(Call("f", m), D(2)))),
        ]));
    }

    private static Formula HalvingFormula()
    {
        Formula m = F.Id("m");
        return Disp(Seq(Bound(m), Parenthesized(AtLeastOne(m)), Sp, Rightarrow, Sp,
            Equal(Cast(A(Product(D(2), m))), Cast(A(m)))));
    }

    private static Formula HalvingViaSquareFormula()
    {
        Formula m = F.Id("m");
        Formula square = new Formula.Power(Cast(A(m)), D(2));
        return Disp(Seq(Bound(m), Parenthesized(AtLeastOne(m)), Sp, Rightarrow, Sp,
            Parenthesized(Equal(Cast(A(Product(D(2), m))), square)), Sp, Land, Sp,
            Parenthesized(Equal(square, Cast(A(m))))));
    }

    private static Formula OddIndexFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound(n), Parenthesized(Less(D(1), n)), Sp, Rightarrow, Sp,
            Call("Odd", n), Sp, Rightarrow, Sp, Equal(Cast(A(n)), D(0))));
    }

    private static Formula CharacterizationFormula()
    {
        Formula n = F.Id("n");
        Formula r = F.Id("r");
        Formula power = Seq(Exists, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            Equal(n, new Formula.Power(D(2), r)));
        return Disp(Seq(Bound(n), Parenthesized(AtLeastOne(n)), Sp, Rightarrow, Sp,
            Parenthesized(Seq(Call("Odd", A(n)), Sp, Leftrightarrow, Sp, Parenthesized(power)))));
    }

    private static Formula Convolution(string name, Formula n)
    {
        Formula k = F.Id("k");
        return FiniteSum(k, Interval(n), Product(Call(name, k), Call(name, Difference(n, k))));
    }

    private static Formula FiniteSum(Formula k, Formula set, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, set)), Sp, summand);

    private static Formula Interval(Formula n) => Call("Icc", D(1), Difference(n, D(1)));
    private static Formula A(Formula n) => Call("a", n);
    private static Formula Cast(Formula n) => Call("cast", n, ModTwo());
    private static Formula ModTwo() => Call("ZMod", D(2));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bound(Formula n) => Seq(Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp);
    private static Formula AtLeastOne(Formula n) => Seq(D(1), Sp, Le, Sp, n);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Difference(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Product(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
