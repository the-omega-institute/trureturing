using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Enclosures;

internal sealed class GoldenAmplitudeEnclosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var amplitude = new Formula.Subscript(Id("A"), Id("h"));
        var center = new Formula.Fraction(Num(3408474), Num(10000000));
        var tolerance = new Formula.Fraction(Num(33), Num(100000000));
        var enclosure = new Formula.Relation(
            new Formula.Absolute(Subtract(amplitude, center)),
            FormulaRelationOperator.LessThanOrEqual,
            tolerance);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The exact golden amplitude satisfies the source's seven-digit enclosure.",
            H("Golden Amplitude Enclosure"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-amplitude-seven-digit-enclosure"),
                    DeclarationHandle.Create(
                        "D5/S3/Constants/Enclosures/GoldenAmplitudeEnclosure."
                        + "ah_seven_digit_enclosure"),
                    H("The golden amplitude lies in its certified decimal interval"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(enclosure)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The amplitude A_h is the canonical exact value "
                            + "(5 sqrt(5) - 3) / 24. Exact rational square comparisons "
                            + "place sqrt(5) between 2.236065936 and 2.236069104; linear "
                            + "arithmetic then proves that A_h differs from 0.3408474 by "
                            + "at most 0.00000033. No floating-point premise is used."))),
                    DescribeRole.Theorem)),
            []));
    }
}
