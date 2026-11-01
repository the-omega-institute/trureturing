using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class BufferedConeExtensionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/BufferedConeExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite buffered mixed old/new graph retains every old whole path and has one outer-buffer tracer for every new whole path.",
        H("Buffered Whole-Path Retained-Cone Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("buffered-whole-path-retained-cone"),
                DeclarationHandle.Create(Owner + "buffered_whole_path_extension"),
                H("Finite mixed-buffer graph extension"),
                StatementSource.FromAuthor(FormulaFor()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
                Blocks(
                    Paragraph(Text(
                        "For finite old and new discrete alphabets, closed inner buffers are placed "
                        + "inside old P/C and new D interiors. A compactness transfer cover and the "
                        + "existing finite-open-cover HasShadowing contract produce a finite control "
                        + "cover T.")),
                    Paragraph(Text(
                        "The graph has vertices V×T×B. Its edge relation contains the old edge and "
                        + "one actual point t in X witnessing every old P and new L constraint at "
                        + "both endpoints. The first-coordinate map preserves edges and lifts every "
                        + "specified complete old vertex path, retaining its time-zero vertex.")),
                    Paragraph(Text(
                        "One shadowing tracer serves an entire new path, placing all its iterates in "
                        + "the outer C/D interiors. Conversely, one specified source x lifts every "
                        + "complete old-K/new-L name. This is a fixed finite cone result; it does not "
                        + "supply the global uniform-follower lemma or solve Peng Question 5.1."))),
                DescribeRole.Theorem))));

    private static Formula FormulaFor() =>
        Seq(F.Id("buffered_whole_path_extension"), Open, F.Id("finite-old-graph"), Comma, Sp,
            F.Id("mixed-buffer-edge-witnesses"), Comma, Sp,
            F.Id("whole-path-lift"), Comma, Sp,
            F.Id("outer-buffer-soundness"), Close);
}
