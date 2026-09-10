using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitProductSlicesDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix = "D5/S1/Digit/DigitProductSlices.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decimal numbers over digits 2, 3, and 6 with at most one digit 3 admit complete divisibility classifications.",
        H("Digit-Product Slices over Digits 2, 3, and 6"),
        Blocks(
            Paragraph(Text(
                "For a natural number N, digitProduct is the product of its base-ten digits, "
                    + "AllDigitsIn236 says that every digit belongs to the set {2,3,6}, and "
                    + "countThree counts occurrences of the digit 3.")),
            Describe.Lean(
                DescribeId.Create("zero-three-slice"),
                DeclarationHandle.Create(DeclarationPrefix + "zero_three_slice"),
                H("The positive zero-3 slice consists exactly of 2 and 6"),
                StatementSource.FromAuthor(ZeroThreeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive natural number with only the permitted digits and no digit "
                        + "3, divisibility by the digit product is equivalent to being 2 or 6. "
                        + "The positivity premise is essential because the base-ten digit list "
                        + "of zero is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-three-slice"),
                DeclarationHandle.Create(DeclarationPrefix + "one_three_slice"),
                H("The unique-3 slice consists exactly of 3, 36, and 2232"),
                StatementSource.FromAuthor(OneThreeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Removing the unique digit 3 shows that two to the power length minus "
                            + "one divides the digit product. At length at least five, this forces "
                            + "divisibility by 16.")),
                    Paragraph(Text(
                        "A kernel-checked exhaustion of the 81 four-digit words over {2,3,6}, "
                            + "restricted to suffixes containing at most one digit 3, rules out "
                            + "divisibility by 16. The remaining lists of length at most four are "
                            + "exhausted in the kernel and leave exactly 3, 36, and 2232. No claim "
                            + "is made about numbers containing two or more digits 3."))),
                DescribeRole.Theorem))));

    private static Formula ZeroThreeFormula()
    {
        Formula natural = F.Id("N");
        Formula hypotheses = Seq(
            D(0), Sp, Lt, Sp, natural,
            Sp, Land, Sp, Call(F.Id("AllDigitsIn"), D(2, 3, 6), natural),
            Sp, Land, Sp, Call(F.Id("countThree"), natural), Sp, Eq, Sp, D(0));
        Formula alternatives = Seq(
            natural, Sp, Eq, Sp, D(2),
            Sp, Lor, Sp,
            natural, Sp, Eq, Sp, D(6));

        return SliceFormula(natural, hypotheses, alternatives);
    }

    private static Formula OneThreeFormula()
    {
        Formula natural = F.Id("N");
        Formula hypotheses = Seq(
            Call(F.Id("AllDigitsIn"), D(2, 3, 6), natural),
            Sp, Land, Sp, Call(F.Id("countThree"), natural), Sp, Eq, Sp, D(1));
        Formula alternatives = Seq(
            natural, Sp, Eq, Sp, D(3),
            Sp, Lor, Sp,
            natural, Sp, Eq, Sp, D(3, 6),
            Sp, Lor, Sp,
            natural, Sp, Eq, Sp, D(2, 2, 3, 2));

        return SliceFormula(natural, hypotheses, alternatives);
    }

    private static Formula SliceFormula(
        Formula natural,
        Formula hypotheses,
        Formula alternatives) => Disp(new Formula.Aligned([
            Seq(Forall, Sp, natural, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(hypotheses, Sp, Implies, Sp),
            Seq(
                Parenthesized(Seq(
                    Call(F.Id("digitProduct"), natural), Sp, Mid, Sp, natural,
                    Sp, Iff, Sp, Parenthesized(alternatives))),
                Dot),
        ]));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(
        Formula name,
        Formula nameSuffix,
        Formula argument) =>
        Seq(Operatorname, Grp(name, nameSuffix), Parenthesized(argument));

    private static Formula Call(Formula name, Formula argument) =>
        Seq(Operatorname, Grp(name), Parenthesized(argument));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
