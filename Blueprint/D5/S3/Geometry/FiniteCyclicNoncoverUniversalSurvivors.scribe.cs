using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

// Source mirrors only. Native projection, ownership and coverage are OPEN.
internal sealed class FiniteCyclicNoncoverUniversalSurvivorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cyclic noncover source construction.", H("FiniteCyclicNoncoverUniversalSurvivors"),
        Blocks(
            Paragraph(Text("Universal proof bodies are attempted source. No compiler, kernel, Scribe/Reg audit or admission was executed. Every handle names its exact D5 source owner. Section variables below are lexical context only, not an asserted compiled telescope. FromLean requests the native projection; no fixture or readout is fabricated.")),
            Node("decl-1", "remaining_zero", "remaining_zero", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :\n    remainingFaces (show 3 ≤ 3*q by omega) s =\n      insert {point (by omega) s} {criticalA q hq s, criticalB q hq s}", DescribeRole.Theorem),
            Node("decl-2", "remaining_one", "remaining_one", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :\n    remainingFaces (show 3 ≤ 3*q+1 by omega) s =\n      insert {point (by omega) s} {criticalOne q s}", DescribeRole.Theorem),
            Node("decl-3", "remaining_two", "remaining_two", "Exact uncompiled source contract. No compiled telescope, projection or acceptance is asserted.", "variable {V : Type*} [Fintype V] [DecidableEq V]\n\ntheorem remaining_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :\n    remainingFaces (show 3 ≤ 3*q+2 by omega) s =\n      insert {point (by omega) s} {criticalTwo q hq s}", DescribeRole.Theorem))));
    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, string rawContract, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose)), Paragraph(Text(rawContract))), role);
}
