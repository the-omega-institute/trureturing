using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class LocalBasicsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Basics", H("Local Basics"),
        Blocks(
            Paragraph(Text("Principal units, places above q, primes 1 mod m split in cyclotomic fields.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalBasics.principalUnits"),
                H("principalUnits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The principal units of the valuation subring B of ℚ̄ (elements congruent to 1 modulo its maximal ideal), as a subgroup of ℚ̄^× written additively.")))))));
}
