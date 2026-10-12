using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class DelayedAtomTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/DelayedAtomTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A later insertion excludes a short closed pulse",
        H("DelayedAtomTransport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("curve-difference"),
                DeclarationHandle.Create(Prefix + "curve_difference"),
                H("Price loss is the integrated weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a price curve on x>1 with derivative minus its continuous positive nonincreasing weight, and 1<a<=b, price(a)-price(b) equals the interval integral of weight over [a,b].")),
                    Paragraph(Text("This is a consumed fundamental-calculus helper for the slope estimate, finite pulse accounting, and the original error bound. It is not claimed as new mathematical content."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("curve-slope-bounds"),
                DeclarationHandle.Create(Prefix + "curve_slope_bounds"),
                H("Endpoint bounds for the price loss"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the same curve and 1<a<=b, (b-a)*weight(b)<=price(a)-price(b)<=(b-a)*weight(a).")),
                    Paragraph(Text("The integral identity and the nonincreasing weight give both endpoint bounds. The delayed-atom exclusion consumes the lower and upper estimates."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("delayed-atom-exclusion"),
                DeclarationHandle.Create(Prefix + "delayed_atom_exclusion"),
                H("A later insertion excludes a short closed pulse"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let price have derivative minus weight on x>1, with continuous positive nonincreasing weight. For y<a+1, t>1, h>0 and C>=t, assume h*price(y)<=the integral from C to C+h of price and 2*weight(t)<h*weight(t+h). Then t is outside the closed interval [a,y].")),
                    Paragraph(Text("The average price over [t,t+h] loses at least h*weight(t+h)/2 from price(t). Shifting the average to C can only decrease it. Contact would give price(t)-price(y)<weight(t), contradicting the paid density. The original integer specialization proves both insertion compatibility and density; no interpolated integer maximizer is assumed.")),
                    Paragraph(Text("The compact reference kernel uses t<z<=B, while the strict actual kernel uses t<=z<=B. Before exclusion, the actual initial atom has weight (price(t)-price(B))/D and the reference initial atom has weight zero. Both terminal weights are zero. These kernels take a price parameter and do not define another original arithmetic price."))
                ), DescribeRole.Theorem))));
}
