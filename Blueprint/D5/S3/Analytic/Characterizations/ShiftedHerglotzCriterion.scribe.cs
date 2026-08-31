using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class ShiftedHerglotzCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Characterizations/ShiftedHerglotzCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive value Cayley scaling identifies Schur maps with Herglotz maps, with the "
            + "ordinary-quotient premises and totalized edge cases made explicit.",
        H("Shifted Herglotz Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-on-upper-half-plane"),
                DeclarationHandle.Create(Prefix + "IsSchurOnUpperHalfPlane"),
                H("Schur maps on the upper half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A Schur map is complex differentiable on the upper half-plane and has "
                        + "pointwise norm at most one there."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("herglotz-on-upper-half-plane"),
                DeclarationHandle.Create(Prefix + "IsHerglotzOnUpperHalfPlane"),
                H("Herglotz maps on the upper half-plane"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A Herglotz map is complex differentiable on the upper half-plane and "
                        + "has nonnegative imaginary part there."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shifted-cayley-transform"),
                DeclarationHandle.Create(Prefix + "shiftedCayleyTransform"),
                H("The shifted value Cayley transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source transform sends u to i divided by omega times the quotient "
                        + "of one minus u by one plus u."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shifted-cayley-imaginary-part"),
                DeclarationHandle.Create(Prefix + "shifted_cayley_imaginary_part"),
                H("Exact imaginary-part identity"),
                StatementSource.FromAuthor(ImaginaryPartFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Direct complex algebra expresses the imaginary part as the disk norm "
                        + "defect divided by the scale denominator, including totalized zeros."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shifted-cayley-positive-imaginary-part"),
                DeclarationHandle.Create(
                    Prefix + "shifted_cayley_positive_imaginary_part"),
                H("Strict positivity is the strict disk inequality"),
                StatementSource.FromAuthor(StrictPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive omega, strict positivity of the imaginary part is equivalent "
                        + "to the strict unit-disk inequality, including at the totalized pole."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shifted-herglotz-criterion"),
                DeclarationHandle.Create(Prefix + "shifted_herglotz_criterion"),
                H("Schur-Herglotz equivalence"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forward direction recovers theta by the inverse Cayley quotient. "
                            + "The reverse direction differentiates the source quotient and uses "
                            + "the exact imaginary-part identity.")),
                    Paragraph(Text(
                        "The source's word inner uses its preceding boundary-unitarity context. "
                            + "That boundary property is not true for arbitrary Schur maps and is "
                            + "therefore not asserted by this generic criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-scale-is-necessary"),
                DeclarationHandle.Create(Prefix + "positive_scale_is_necessary"),
                H("Positive scale is necessary"),
                StatementSource.FromAuthor(ScaleWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At scale zero the totalized transform of the constant two is Herglotz "
                        + "although that constant is not Schur. At scale minus one, the constant "
                        + "zero is Schur but its transform is not Herglotz."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("denominator-nonvanishing-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "denominator_nonvanishing_is_necessary"),
                H("Denominator nonvanishing is necessary"),
                StatementSource.FromAuthor(DenominatorWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Changing the constant one to minus one at i gives a discontinuous map. "
                        + "Totalized division sends both values to zero, so the Cayley image "
                        + "is Herglotz while the original map is not Schur."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degenerate-function-audit"),
                DeclarationHandle.Create(Prefix + "degenerate_function_audit"),
                H("Degenerate function audit"),
                StatementSource.FromAuthor(DegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant minus one exposes the zero denominator and totalized quotient. "
                        + "The identity map fails the Schur bound at two i."))),
                DescribeRole.Theorem))));

    private static Formula ImaginaryPartFormula()
    {
        Formula omega = F.Id("omega");
        Formula u = F.Id("u");
        Formula numerator = Subtract(D(1), Call("normSq", u));
        Formula denominator = Seq(omega, Sp, Call("normSq", Add(D(1), u)));
        Formula identity = Relation(
            Call("Im", Call("shiftedCayleyTransform", omega, u)),
            Eq,
            new Formula.Fraction(numerator, denominator));
        return Quantified(omega, u, identity);
    }

    private static Formula StrictPositivityFormula()
    {
        Formula omega = F.Id("omega");
        Formula u = F.Id("u");
        Formula premise = Relation(D(0), Lt, omega);
        Formula positive = Relation(
            D(0), Lt, Call("Im", Call("shiftedCayleyTransform", omega, u)));
        Formula disk = Relation(Call("norm", u), Lt, D(1));
        return QuantifiedImplication(omega, u, premise, IffFormula(positive, disk));
    }

    private static Formula CriterionFormula()
    {
        Formula omega = F.Id("omega");
        Formula theta = F.Theta;
        Formula premise = And(
            Relation(D(0), Lt, omega),
            Call("NonvanishingOnUpperHalfPlane", Add(D(1), theta)));
        Formula cayleyMap = Call("shiftedCayleyTransform", omega, theta);
        Formula criterion = IffFormula(Call("Herglotz", cayleyMap), Call("Schur", theta));
        return QuantifiedImplication(omega, theta, premise, criterion);
    }

    private static Formula ScaleWitnessFormula()
    {
        Formula zeroScale = Call("Herglotz", Call("shiftedCayleyTransform", D(0), D(2)));
        Formula notTwo = Not(Call("Schur", Call("const", D(2))));
        Formula zeroSchur = Call("Schur", Call("const", D(0)));
        Formula negative = Not(Call(
            "Herglotz",
            Call("shiftedCayleyTransform", Seq(Minus, D(1)), D(0))));
        return Disp(And(zeroScale, And(notTwo, And(zeroSchur, negative))));
    }

    private static Formula DenominatorWitnessFormula()
    {
        Formula theta = Call(
            "update", Call("const", D(1)), F.Id("i"), Seq(Minus, D(1)));
        Formula image = Call("shiftedCayleyTransform", D(1), theta);
        Formula noDenominator = Not(Call(
            "NonvanishingOnUpperHalfPlane", Add(D(1), theta)));
        return Disp(And(
            Call("Herglotz", image),
            And(Not(Call("Schur", theta)), noDenominator)));
    }

    private static Formula DegenerateFormula()
    {
        Formula minusOne = Call("const", Seq(Minus, D(1)));
        Formula noDenominator = Not(Call(
            "NonvanishingOnUpperHalfPlane", Add(D(1), minusOne)));
        Formula image = Call("shiftedCayleyTransform", D(1), minusOne);
        return Disp(And(
            Call("Schur", minusOne),
            And(noDenominator, And(Call("Herglotz", image),
                Not(Call("Schur", F.Id("id")))))));
    }

    private static Formula QuantifiedImplication(
        Formula first, Formula second, Formula premise, Formula conclusion) =>
        Quantified(
            first,
            second,
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));

    private static Formula Quantified(
        Formula first, Formula second, Formula conclusion) => Disp(Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp, conclusion));

    private static Formula Relation(
        Formula left, Formula relation, Formula right) => Seq(
            left, Sp, relation, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Not(Formula value) => Seq(Neg, Sp, value);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }
            pieces.Add(arguments[index]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
