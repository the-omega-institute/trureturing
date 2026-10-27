using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class M5SourceArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hard source geometry and an attained initial height.",
        H("Hard source geometry and an attained initial height"),
        Blocks(
            Paragraph(Text("PrefixArithmetic is the common source prefix record. The original four prefix proofs arithmetic_geometry, canonical_mask_height, gate_limits and wj_geometry take this record directly. The M5 Arithmetic record adds a0, a<=a0<=z and oddness only for its specialized tail. This visibility and dependency split preserves the M5 source hypotheses and supplies the generic LOWER prefix without an a0<=z assumption.")),
            Paragraph(Text("Write q=H/2, P0=H/4, K=w-n, g=(w-1)/2. The original source inequalities imply a<=n<z<b<w, H*Delta<n, and z<=2a-3. There are integers 1<=A<=P0 and 0<=f<=g with 2f=n+w+Delta-2A*K. The adjacent inequalities 2K(A-1)<n+Delta+1<=2K*A select an actual binary-mask coefficient.")),
            Paragraph(Text("The W_J construction has final height Z=f+P+J, with 0<Z and 2Z<=v-1. For the later T gate, ell=(u-z)/2, hi=u-(z+1)/2 and W=(u-1)/2 satisfy ell>0 and hi=ell+W. Odd source seeds make all displayed half-differences exact integers.")),
            Paragraph(Text("When F=H/2, the source also implies u<2z, H*u>=N+1, n<H^2*Delta, n>2H, b1>2n and u>b. The lower branch F<=H/4 instead gives u>2z. The two branches have different literal T selections."))), []));
}
