using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Variable triangular lengths admit square-integrable comparisons.",
        H("Variable triangular lengths admit square-integrable comparisons"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("triangular-average-variable-mem-lp"),
                DeclarationHandle.Create(Prefix + "triangularAverage_variable_memLp"),
                H("Square integrability with measurable lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be measurable and bounded on every compact interval. On a finite ordered interval [a,b], let the measurable length H(x) lie between fixed positive l and finite L. Then the triangular average B_H(x)(x)/H(x)^2 belongs to L squared on that interval. Measurability follows by expressing B_h(x) through the continuous primitive of E and h E(x); compact boundedness gives a uniform bound 2M/l."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("variable-average-square-error-le"),
                DeclarationHandle.Create(Prefix + "variable_average_square_error_le"),
                H("The error from freezing a length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose h>0, 0<=d<=h, and the measurable length H(x) lies in [h,h+d] on [a,b]. If every increment of length u in [h,h+d] has square integral at most M on [a,b], then the square integral of P_H(x)(x)-P_h(x) is at most 18(d/h)^2 times the square integral of P_h plus 2d^2 M/h^4. Split the difference into the change of the denominator and the primitive tail. Cauchy-Schwarz bounds the latter by d times the integral of the increment squares over the length strip; Fubini gives the factor dM."))),
                DescribeRole.Theorem))));
}
