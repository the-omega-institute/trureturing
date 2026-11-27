using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat;

internal sealed class FloorGroupsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Floor Groups", H("Floor Groups"),
        Blocks(
            Paragraph(Text("Flag stabilisers, unipotent radicals, Levi factors and Weyl-torus elements of a unitary group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/FloorGroups.unitriGroup_dual_row"),
                H("unitriGroup_dual_row"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For s in Q_j and a < j (hyperbolic pairs indexed from 0), the row of s at e*_a equals that of the identity matrix in every column other than those of the e*_b with b < a.")))))));
}
