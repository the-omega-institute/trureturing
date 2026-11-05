using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class M5AttainedMeshDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary selection with actual depleted support.",
        H("Binary selection with actual depleted support"),
        Blocks(
            Paragraph(Text("For a subset S of Fin(length), its weight is the sum of the powers 2^j over its literal indices. Every integer from zero to 2^length-1 has such a mask. Complementary masks have weights adding to 2^length-1. If only S remains available, a supported round-up above d overshoots by at most the weight of the missing complement. This bound preserves the actual depleted support.")),
            Paragraph(Text("Write e=2^length(row after J), so the v row has a nonempty SMALL interior exactly when e>=2. In the half-power branch with e>=2, the canonical coefficient is A=1. A finite crossing using the two positive step sizes 2b-w and u-b produces coefficients for retained n,w,b labels and actual u payment. With e=1, either the surviving w support spans the gate or a construction retaining n,z,b and paying u crosses it. The borrowing endpoint includes the small H=8,A=2 case.")),
            Paragraph(Text("In the lower branch, consecutive multiples c*z meet the T gate for some 0<=c<=q-1. These selections use masks of the present physical rows, without a hypothesis about an untouched reserve, interval density or future continuation."))), []));
}
