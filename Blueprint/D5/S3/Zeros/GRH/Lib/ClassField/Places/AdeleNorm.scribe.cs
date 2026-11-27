using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class AdeleNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adele Norm", H("Adele Norm"),
        Blocks(
            Paragraph(Text("Ideles to ideals and class group; large S; open subgroups that contain the principal ideles of totally positive elements have finite index. Dirichlet–Chevalley–Hasse S-unit theorem: finite generation and rank. Norm map on finite adeles of an extension and its basic properties.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/AdeleNorm.adeleNorm_locIdele"),
                H("adeleNorm_locIdele"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For number fields L/K, a finite place w of L and y in L_w^×, the norm to K of the finite idele that is y at w and 1 elsewhere is 1 at every place except the one below w.")))))));
}
