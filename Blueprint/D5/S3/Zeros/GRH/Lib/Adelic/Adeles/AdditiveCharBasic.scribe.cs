using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class AdditiveCharBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Additive Char Basic", H("Additive Char Basic"),
        Blocks(
            Paragraph(Text("Standard additive character: conductor is the different, non-degeneracy, field is own annihilator.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdditiveCharBasic.mem_ratAdeles_of_psi"),
                H("mem_ratAdeles_of_psi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a totally complex number field E, an adele x with ψ(ax) = 1 for all a in E lies in the diagonal image of E; here ψ is the standard additive character stdAddChar of the adeles.")))))));
}
