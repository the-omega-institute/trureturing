using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class PointFunctionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Point Functions", H("Point Functions"),
        Blocks(
            Paragraph(Text("Regular functions via functor of points: evaluation, gluing, fpqc descent of functions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/PointFunctions.ext_of_dominant"),
                H("ext_of_dominant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let p: Y → X be quasi-compact and scheme-theoretically dominant, V_a the cover of M on Y. Functions f, g regular on U agree on U if their pull-backs agree on each p⁻¹U ∩ V_a.")))))));
}
