using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class ArithmeticResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed arithmetic estimates for the Möbius window",
        H("Monotone weights on the Chebyshev terms"),
        Blocks(
            Paragraph(Text("The signed Chebyshev truncation beyond m uses the decreasing weights "
                + "ψ(x^(1/n)) and finite Möbius prefix sums. A geometric majorant bounds the sum "
                + "of the weights and leaves the factor m/log(m+1) after normalization and "
                + "integration over the positive tail.")),
            Paragraph(Text("For 0 ≤ u ≤ L(m+1), use the omitted degrees 2n ≥ m+1. Separate the "
                + "centered root term into the uncentered Chebyshev tail and its arithmetic "
                + "power. Each weight is nonnegative and decreasing in n. The first omitted "
                + "weight is at most a constant depending on L times exp(−u/2). The signed "
                + "Möbius prefix bound then gives order m/log m for their difference.")))));
}
