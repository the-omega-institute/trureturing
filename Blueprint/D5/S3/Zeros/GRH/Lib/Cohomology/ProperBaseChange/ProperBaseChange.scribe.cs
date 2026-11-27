using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange;

internal sealed class ProperBaseChangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper Base Change", H("Proper Base Change"),
        Blocks(
            Paragraph(Text("Proper base change: closed fibre over an absolutely integrally closed valuation ring, F_l coefficients.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ProperBaseChange.proper_base_change"),
                H("proper_base_change"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Proper base change: for a functor Y proper over an absolutely integrally closed valuation ring A and ℓ a prime invertible in A, restriction from Y to its closed fibre is bijective on all cohomology groups with coefficients ℤ/ℓ.")))))));
}
