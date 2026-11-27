using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class LateWindowSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "High-frequency sampling with the actual degree spacing",
        H("Control the value and its derivative in separate square sums"),
        Blocks(
            Paragraph(Text("Assume RH and fix 0<η<1/2. For q≥3, u≥q and integer H≥1, "
                + "keep every member of an arbitrary finite set of actual zero occurrences whose "
                + "frequency bin k has |k|>H. The bin k consists of frequencies in (k,k+1].")),
            Paragraph(Text("For n from ceil(q/2) to q, evaluate the retained finite mode at u/n "
                + "and multiply its norm by exp(−u/q+u/(2n)). The sum of these weighted norms "
                + "is bounded by Cη times the sum [(1+q²/u)H^(η−1/2)+q^(1/2+η)], with one constant "
                + "for all q, u, H and finite occurrence sets.")),
            Paragraph(Text("For the base coefficient and for each adjacent-degree difference, bound "
                + "the phase derivative both by the bin frequency times the coefficient bound and by its "
                + "degree-dependent bound. Take the minimum to obtain "
                + "a multiple of min(q,1+|k|)(1+|k|)^(η−1). Splitting at 1+|k|=q bounds "
                + "the square sum by a constant times q^(1+2η).")),
            Paragraph(Text("Apply the local integral bounds at separation min(1,u/q²). "
                + "The coefficient differences telescope in degree. The exponential weight "
                + "makes the bounds over unit intervals sum geometrically.")))));
}
