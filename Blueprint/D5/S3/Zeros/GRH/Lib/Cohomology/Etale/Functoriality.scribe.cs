using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class FunctorialityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Functoriality", H("Functoriality"),
        Blocks(
            Paragraph(Text("Functoriality of Ext of abelian presheaves in both variables and along exact functors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Functoriality.dimension_shift_induction"),
                H("dimension_shift_induction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Induction on Ext classes out of N: a property holds for every class if it holds for morphisms N → F and, for each short exact 0 → S₁ → S₂ → S₃ → 0, passes from x in Ext^n(N,S₃) to its image in Ext^{n+1}(N,S₁).")))))));
}
