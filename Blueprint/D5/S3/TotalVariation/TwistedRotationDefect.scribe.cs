using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TwistedRotationDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TwistedRotationDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complemented rotation preserves full path weights and forces a uniform same-rule defect bound.",
        H("Twisted Rotation and Parry Window Defects"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twistedrotationdefect-rotation-preserves-weight"),
                DeclarationHandle.Create(Prefix + "rotation_preserves_weight"),
                H("Rotation of the signed state path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k and m and every real parameter p, consider a word v of m+1 states "
                    + "in Bool times Fin k. Extend it to natural times by complementing the absolute sign "
                    + "after each turn and repeating the suffix coordinate. The rotation equivalence sends "
                    + "v to its tail followed by the complement of its first state. Its inverse prepends "
                    + "the complement of the last state to the initial segment. At every natural time i, "
                    + "the extension of the rotated word equals the original extension at i+1. The product "
                    + "of all m+1 transition weights, including the edge to the complemented start, is "
                    + "unchanged by rotation. The equality uses the actual reset kernel and holds for "
                    + "every p; no nonnegativity hypothesis is needed for this product identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twistedrotationdefect-parry-window-lower-bound"),
                DeclarationHandle.Create(Prefix + "parry_window_lower_bound"),
                H("Uniform bound for each fixed deterministic rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k >= 2, R >= 1 and G >= 1, and every fixed deterministic table "
                    + "f : (Fin R -> Bool) -> Bool, put L = R+1+G. The actual twisted prefix defect "
                    + "probability twistedDefect k R G f is at least 1/L. The actual stationary Parry "
                    + "defect probability stationaryDefect k R f is at least "
                    + "1/L - 2L(3/4)^(G/3) - Real.goldenRatio^(2-L). Here G/3 is natural division "
                    + "and 2-L is an integer exponent. The same table is applied to both adjacent "
                    + "R-bit relation windows. Complete signed state prefixes have the existing "
                    + "twistedLaw distribution: full transition products are divided by loopMass, "
                    + "with no initial stationary factor. Splitting a full path into its prefix and "
                    + "closing continuation identifies the window event exactly, including windows "
                    + "that cross the complemented seam after rotation. Each signed cycle has a "
                    + "same-rule defect; rotation makes the weighted expectations equal. The stationary "
                    + "comparison then gives the second inequality, without a small-error assumption. "
                    + "Moreover, there exists a deterministic table fmin whose actual stationary defect is "
                    + "no greater than that of any table of the same window length, and its attained "
                    + "minimum satisfies the same lower bound."))),
                DescribeRole.Theorem))));
}
