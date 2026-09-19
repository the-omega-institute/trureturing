using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class SignedSquaresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sign-safe squares and norm squares.",
        H("Sign-safe squares and norm squares"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signedsquares-square-factory-correct"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_factory_correct"),
                H("Checked square expressions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every accepted annotated rational expression, squareBounds chooses the correct lower square endpoint on positive or negative intervals and zero on intervals crossing zero. Its upper endpoint is the maximum of the two endpoint squares. The resulting square expression passes the checker and encloses the real square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signedsquares-square-bounds-width-le"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.square_bounds_width_le"),
                H("Square width on a bounded interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For -A<=l<=u<=A with A nonnegative, the square bounds are nonnegative and ordered, their upper endpoint is at most A^2, and their width is at most 2A(u-l)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signedsquares-norm-sq-difference-width-le"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/SignedSquares.norm_sq_difference_width_le"),
                H("Two signed differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two pairs of ordered intervals in [-Ap,Ap] and [-Aq,Aq], subtracting opposite endpoints and summing the two square intervals gives an ordered nonnegative norm-square interval. Its upper endpoint is at most (2Ap)^2+(2Aq)^2, and its width is bounded by four times each amplitude times the sum of the corresponding two input widths."))),
                DescribeRole.Theorem)),
        []));
}
