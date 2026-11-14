using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;
internal sealed class SelectedSemialgebraicConnectedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected semialgebraic connected source.",
        H("Selected semialgebraic connected source"),
        Blocks(Paragraph(Text("This selection from TauCetiProject/TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9 retains CAD/Basic.sUnion_sep_subset; CAD/Existence.exists_isCAD_subset_or_disjoint; Semialgebraic/Connected partition declarations. It consumes the actual old CAD producer and real projection instance at revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2. The proofs construct finite connected semialgebraic partitions and semialgebraic closures from their original inputs; these outputs are not supplied as assumptions. The original source ownership and Apache-2.0 license are retained in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. No independent escape credit is claimed. Retire each adaptation when the actual pinned mathlib supplies an equivalent statement.")))));
}
