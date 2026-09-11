using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcFiniteCollections;

internal sealed class OrderDenseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ZfcFiniteCollections/OrderDense.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable dense families admit a generic preorder filter through any prescribed element.",
        H("OrderDense"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countable-generic-filter"),
                DeclarationHandle.Create(Prefix + "exists_genericFilter_of_countable"),
                H("A generic filter through a prescribed element"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Id("D"), F.Comma, F.Sp, Id("a"), F.Comma, F.Sp, Call("Countable", Id("D")), F.Implies, F.Sp, F.Exists, F.Sp, Id("G"), F.Comma, F.Sp, Call("IsGeneric", Id("G"), Id("D")), F.Land, F.Sp, Id("a"), F.InMacro, F.Sp, Id("G")))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any preorder, D ranges over families of downward dense sets and a over its elements. If D is countable, there is a nonempty, upward-closed, downward-directed filter G containing a and meeting every set in D. The countable family itself supplies an encodable index type, even when it is empty. On the dual order, each dense set is cofinal. The ideal supplied by Mathlib contains a and meets each indexed set; wrapping that ideal as a preorder filter gives the claim."))),
                DescribeRole.Theorem),
            Paragraph(Text("Downward density means that every element has a smaller or equal element in the set. Genericity means that the filter meets each dense set in the given family.")),
            Paragraph(Text("The bundled density and genericity interface follows FormalizedFormalLogic/Foundation. The existence proof applies Mathlib idealOfCofinals, mem_idealOfCofinals and cofinal_meets_idealOfCofinals. Attribution and the Apache-2.0 license are in Library/ConceptDynamics/foundation2026firstorder.md.")))));
}
