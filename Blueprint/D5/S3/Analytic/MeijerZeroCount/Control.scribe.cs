using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MeijerZeroCount;

internal sealed class ControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single interior zero for the control function.",
        H("The two-component control family"), Blocks(
            Describe.Lean(DescribeId.Create("meijer-control-single-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/MeijerZeroCount/Control.zeros_control"),
                H("Exactly one control zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive natural numbers n and d and any real c, take a=(n+c,n+c) and b=(c,2n+d+c). The control function has exactly one zero in the interval from zero to one, with both endpoints excluded.")),
                    Paragraph(Text("For positive x, the function is x to the power c times 2x to the power n minus one minus x to the power 2n+d. Factoring the latter expression by x-1 leaves the geometric-sum polynomial H(x)=sum over i below n of x to the power i minus x to the power n times the sum over i below n+d of x to the power i. Its endpoint values are one and minus d, so continuity gives an interior zero.")),
                    Paragraph(Text("After division by x to the power n, the first sum consists of real powers with negative exponents. Every such term strictly decreases on the positive axis. Every term of the second sum is nondecreasing. The resulting difference strictly decreases, which gives uniqueness. The factors x to the power c and x-1 do not vanish in the interval."))),
                DescribeRole.Theorem))));
}
