using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class OccurrenceBinMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-root masses of actual zero occurrences",
        H("Uniform estimates over unit bins"),
        Blocks(
            Paragraph(Text("Each occurrence indexes a nontrivial zero with its analytic multiplicity. "
                + "The count in the half-open unit bin indexed by k is bounded by a constant "
                + "times log(3+|k|).")),
            Paragraph(Text("RH and the ordinate constraint give an inverse root norm of order (1+|k|)^(−1). "
                + "Absorbing the logarithm into any positive power η gives bin mass of order "
                + "(1+|k|)^(η−1).")))));
}
