using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;
internal sealed class PartialSpreadHolesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original seven-dimensional written lower-bound proof.",
        H("PartialSpreadHoles"),
        Blocks(Describe.Lean(DescribeId.Create("law-0"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/PartialSpreadHoles.result"), H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("For every63-point domain and every eight pairwise disjoint seven-point blocks with the stated31-point hyperplanes and7/3 block incidences, counting forces the seven holes to be mutually orthogonal. The actual seven-dimensional graph supplies every incidence hypothesis; no chosen spread is assumed representative."))), DescribeRole.Theorem)),
        []));
}
