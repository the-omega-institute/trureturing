using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

// Source mirrors only. Native projection, ownership and coverage are OPEN.
internal sealed class FiniteCyclicNoncoverUniversalSurvivorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors",
            "Universal original-label cyclic noncover survivors follow from exact interval images, actual ordered suffix conjugacy and named critical-face readback.",
            "original-cyclic-universal-survivors",
            Anchor.ParseCanonical("mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic")), H("FiniteCyclicNoncoverUniversalSurvivors"),
        Blocks(
            Paragraph(Text("Universal proof bodies are attempted source. No compiler, kernel, Scribe/Reg audit or admission was executed. Every handle names its exact D5 source owner. Section variables below are lexical context only, not an asserted compiled telescope. FromLean requests the native projection; no fixture or readout is fabricated.")),
            Node("decl-1", "remaining_zero", "remaining_zero", "The lexical declaration below retains its original parameters and hypotheses.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :\n    remainingFaces (show 3 ≤ 3*q by omega) s =\n      insert {point (by omega) s} {criticalA q hq s, criticalB q hq s}", DescribeRole.Theorem),
            Node("decl-2", "remaining_one", "remaining_one", "The lexical declaration below retains its original parameters and hypotheses.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :\n    remainingFaces (show 3 ≤ 3*q+1 by omega) s =\n      insert {point (by omega) s} {criticalOne q s}", DescribeRole.Theorem),
            Node("decl-3", "remaining_two", "remaining_two", "The lexical declaration below retains its original parameters and hypotheses.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :\n    remainingFaces (show 3 ≤ 3*q+2 by omega) s =\n      insert {point (by omega) s} {criticalTwo q hq s}", DescribeRole.Theorem))));
    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(SourceText(prose), SourceText(rawContract)), role);

    // TextRun is one line. Keep every quoted source line, including blank separators,
    // as typed text; this is commentary, never a substitute for a Lean projection.
    private static DocumentBlock SourceText(string value) => value.Contains('\n')
        ? new DocumentBlock.Section(H("Source text"), Blocks(Array.ConvertAll(
            value.Split('\n'), line => Paragraph(Text(line.Length == 0 ? "Definitions and proofs are in the paired Lean module." : line)))))
        : Paragraph(Text(value));
}
