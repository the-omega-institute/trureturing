using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class GoodCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Good Criterion", H("Good Criterion"),
        Blocks(
            Paragraph(Text("Potentially crystalline with inertia acting trivially on D_pcris implies crystalline. Crystalline iff potentially crystalline with trivial inertia action; a multiple of a killing polynomial kills.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/GoodCriterion.isGoodAt_iff"),
                H("isGoodAt_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("At a place A above a finite place w, r is unramified (crystalline above ℓ) exactly when it is of finite type and X − 1 kills every element of inertia.")))))));
}
