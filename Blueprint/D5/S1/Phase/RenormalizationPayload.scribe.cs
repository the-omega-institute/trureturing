using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class RenormalizationPayloadDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Phase/RenormalizationPayload",
            "The two golden face readings uniquely determine their renormalization map."),
        H("Two-Face Renormalization Is Recoverable"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("two-face-renormalization-is-recoverable"),
                H("Both face readings determine the renormalization map"),
                LeanTheorem(
                    "D5/S1/Phase/RenormalizationPayload.renormalization_payload"),
                Disp(Seq(
                    F.Id("R"), Open, F.Id("x"), Comma, F.Id("y"), Close,
                    Sp, Eq, Sp,
                    Open, Varphi, Sp, F.Id("x"), Comma, Sp,
                    Psi, Sp, F.Id("y"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Consider a map on two real coordinates. If its first coordinate "
                        + "always scales the first input by the golden ratio and its second "
                        + "coordinate always scales the second input by the golden conjugate, "
                        + "then the whole map is uniquely the canonical two-face "
                        + "renormalization. The conclusion is equality of functions, not only "
                        + "agreement at a selected input, so the operator can be recovered "
                        + "extensionally from the pair of readings and is genuine payload.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies `Real.goldenRatio`, `Real.goldenConj`, the "
                        + "two-coordinate vector constructor, function extensionality, and the "
                        + "finite case split. A source search found no declaration packaging "
                        + "this exact two-face recoverability statement, so the Lean theorem "
                        + "is a short new proof rather than a wrapper. The source atom makes a "
                        + "single dependency claim; no analytic limit, model-set density, or "
                        + "generating-series identity is added here.")))
            ))));
}
