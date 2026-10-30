using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciRauzyFractalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The finite Tribonacci internal window has a compact Rauzy closure with the three admissible prefix contractions.",
            H("Tribonacci Rauzy Fractal"),
            Blocks(
                Paragraph(Text(
                    "The construction starts from the existing bounded internal window at a "
                    + "non-Perron Tribonacci root. It proves nonemptiness, compactness, an "
                    + "explicit closed-ball bound, and invariance of the closure under the "
                    + "0, 10, and 110 prefix maps. Exact attractor equality is left open for "
                    + "a later unit.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-closure"),
                    DeclarationHandle.Create("D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal"),
                    H("Rauzy closure"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                        "The closure of the finite Tribonacci internal window in the complex "
                        + "internal coordinate is the Rauzy fractal set."))), DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-prefix-contractions"),
                    DeclarationHandle.Create("D5/S0/Tower/Tribonacci/RauzyFractal.zeroPrefixMap"),
                    H("Prefix contractions"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The three maps are the complex affine maps induced by the admissible "
                        + "initial blocks 0, 10, and 110."))), DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-compact"),
                    DeclarationHandle.Create("D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_isCompact"),
                    H("Nonemptiness and compactness"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The empty name supplies the origin. The existing geometric-series "
                        + "bound makes the closure compact at every secondary root."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-ball-bound"),
                    DeclarationHandle.Create("D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_subset_closedBall"),
                    H("Explicit window bound"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The closure lies in the closed ball centered at zero with radius "
                        + "(1 - ‖z‖)⁻¹."))), DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-rauzy-prefix-invariance"),
                    DeclarationHandle.Create("D5/S0/Tower/Tribonacci/RauzyFractal.rauzyFractal_prefix_invariant"),
                    H("Prefix invariance"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Admissibility transport is proved for each prefix, and continuity "
                        + "transports the inclusions through closure."))), DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/ModelSet")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Names"))
            ]));
    }
}
