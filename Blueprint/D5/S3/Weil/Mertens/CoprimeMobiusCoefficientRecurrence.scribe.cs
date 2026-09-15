using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class CoprimeMobiusCoefficientRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coprime Mobius coefficient under adjoining a prime.",
        H("Prime extension and same-sign overlap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coefficient-recurrence"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.coefficient_recurrence"),
                H("An exact recurrence and strict decrease"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let R be squarefree and greater than one, and let p be a prime not dividing R. "
                    + "The function H is the same-sign overlap of the two truncated Mobius kernels "
                    + "B(R,u) and B(R,u/p), and J is its inverse-square integral over u greater than one. "
                    + "The coefficient c(Rp) equals (1-p to the power minus two)c(R) "
                    + "minus 2e(R)(1-1/p)J(R,p), and is strictly smaller than c(R)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("overlap-integral-positive"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence.overlap_integral_pos"),
                H("Positivity from a same-sign overlap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a squarefree R greater than one and a prime p, suppose that at some real "
                    + "u at least one the two kernels B(R,u) and B(R,u/p) have positive product. "
                    + "Their same-sign overlap persists on an interval of positive length, "
                    + "so J(R,p) is strictly positive."))),
                DescribeRole.Theorem))));
}
