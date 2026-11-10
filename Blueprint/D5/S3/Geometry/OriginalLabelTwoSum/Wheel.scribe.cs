using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum;

internal sealed class WheelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/OriginalLabelTwoSum/Wheel.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/Wheel",
            "The original four-rim-wheel Gamma and two fillings are native evolving free-pair sequences with a separate collar.",
            "original-label-two-sum-wheel",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Wheel"),
        Blocks(
            Node("label", "Label", "Label",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("y", "Y", "Y",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("r", "R", "R",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("z", "Z", "Z",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("e", "E", "E",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("a0", "A0", "A0",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("a1", "A1", "A1",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("b1", "B1", "B1",
                "The declaration uses the original raw label carrier and the stated parameters.", DescribeRole.Definition),
            Node("gamma", "gamma", "gamma",
                "All four ORIGINAL Gamma pairs, in their actual evolving complexes.", DescribeRole.Definition),
            Node("gamma-pairs", "gamma_pairs", "gamma_pairs",
                "Ordered extraction uses the real native pairs.", DescribeRole.Theorem),
            Node("interface-equations", "interface_equations", "interface_equations",
                "A0 is E intersect the original Z-simplex; A1 retains the e-row simplex.", DescribeRole.Theorem),
            Node("fill0", "fill0", "fill0",
                "No pair at all in either list of filling zero.", DescribeRole.Definition),
            Node("fill1", "fill1", "fill1",
                "The collar pair is on B1 alone, while the main endpoint also contains 134.", DescribeRole.Definition),
            Node("collar-not-free-in-main", "collar_not_free_in_main", "collar_not_free_in_main",
                "A concrete obstruction to performing the collar pair in the whole endpoint: two distinct strict cofaces remain there.", DescribeRole.Theorem),
            Node("certificate", "certificate", "certificate",
                "The wheel's absolute certificate is a consumer of the same path E.", DescribeRole.Definition),
            Node("seedlabel", "SeedLabel", "SeedLabel",
                "The wheel's absolute certificate is a consumer of the same path E.", DescribeRole.Definition),
            Node("root", "root", "root",
                "p=0,u=1,v=2; no label is globally removed as a ghost.", DescribeRole.Definition),
            Node("seed", "seed", "seed",
                "p=0,u=1,v=2; no label is globally removed as a ghost.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
