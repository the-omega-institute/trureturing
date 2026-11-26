using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class AdicRingHomExtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adic Ring Hom Ext", H("Adic Ring Hom Ext"),
        Blocks(
            Paragraph(Text("Absolutely integrally closed rings: definition and permanence; Frobenius ring map. Normed fields over Q_p; elementary lemmas on adic separation and completeness. Ring maps to p-adically separated rings agree if they agree on dense elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/AdicRingHomExt.isPrecomplete_of_shiftDiff_surjective"),
                H("isPrecomplete_of_shiftDiff_surjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the maps shiftDiff attached to x and to y, for the commutative ring R as a module over itself, are both surjective, then R is precomplete for the ideal (x,y): every (x,y)-adic Cauchy sequence has a limit.")))))));
}
