using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class HussainA402341CentralCoefficientValuationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/hussain2026a402341");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary digit sum gives the exact valuation of every even-indexed central coefficient.",
        H("Binary valuation of the even central coefficients in A402341"),
        Blocks(
            Paragraph(Text(
                "Write a(n) for the coefficient at degree floor(15n/2) in "
                    + "(1 + x + ... + x^15)^n over the natural numbers. Write v_2 for the 2-adic valuation. "
                    + "Write s_2(m) for the sum of the base-two digits of m, with s_2(0) = 0.")),
            Describe.Lean(
                DescribeId.Create("a402341-even-central-coefficient-valuation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/HussainA402341CentralCoefficientValuation.result"),
                H("Exact valuation at every even index"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At n = 0 the coefficient is 1, so its binary valuation and the digit sum "
                            + "are both zero. Positivity at every even n ensures that the valuation "
                            + "is the exponent of two in a nonzero natural number.")),
                    Paragraph(Text(
                        "The geometric polynomial has an integral expression in the basis "
                            + "x^j(1+x)^(15-2j). For even powers the corresponding change-of-basis "
                            + "polynomial is a power of a square. Pairing off-diagonal products and "
                            + "using the binary carry inequality gives a factor of 2^(1+s_2(j)) "
                            + "at every positive degree j. The diagonal product gains the same "
                            + "factor because doubling preserves digit sum and a positive index has "
                            + "at least one nonzero digit.")),
                    Paragraph(Text(
                        "At central degree m = 15n/2 the constant term in this basis contributes "
                            + "the central binomial coefficient with valuation s_2(m). Every other "
                            + "contribution is divisible by 2^(1+s_2(m)). The sum therefore has the "
                            + "valuation of its central binomial term."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula middle = Seq(Lfloor, Sp, Frac, Grp(Seq(D(1, 5), n)), Grp(D(2)), Sp, Rfloor);
        Formula sum = Seq(Sum, Underscore, Grp(j, Eq, D(0)), Caret, Grp(D(1, 5)),
            Sp, new Formula.Power(x, j));
        Formula coefficient = Seq(OpenBracket, new Formula.Power(x, middle), CloseBracket,
            new Formula.Power(Seq(Open, sum, Close), n));
        Formula even = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Even"))), [n]);
        Formula valuation = new Formula.Apply(new Formula.Subscript(F.Id("v"), D(2)), [coefficient]);
        Formula digitSum = new Formula.Apply(new Formula.Subscript(F.Id("s"), D(2)), [middle]);
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, coefficient);
        Formula exact = new Formula.Relation(valuation, FormulaRelationOperator.Equal, digitSum);
        Formula law = new Formula.Logic(positive, FormulaLogicOperator.And, exact);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Seq(Mathbb, Grp(F.Id("N"))),
            new Formula.Logic(even, FormulaLogicOperator.Implies, law)));
    }
}
