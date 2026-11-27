using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProjectiveLine;

internal sealed class LineChernClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Chern Class", H("Line Chern Class"),
        Blocks(
            Paragraph(Text("Kummer sequence, trivialised Tate twist, and its cup action on torsion coefficient theories. Projective line as functor, cocycle of O(1), first Chern class and its cup operator.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProjectiveLine/LineChernClass.exists_etaClass_supported_diagonal"),
                H("exists_etaClass_supported_diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For sections q, q' of P¹ along g there are compatible ideals J_c, with q = q' wherever J_c = 0, such that q^*η + q'^*η (η = etaClass) comes from H² relative to the locus where J is the unit ideal.")))))));
}
