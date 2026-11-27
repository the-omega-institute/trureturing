using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Hecke;

internal sealed class ClassMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Mean", H("Class Mean"),
        Blocks(
            Paragraph(Text("Integral over double cosets as automorphism-weighted class sum; level change; smooth vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassMean.classIntegral_sum"),
                H("classIntegral_sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Assume HasFiniteType for Γ and K. If F(g) = ∑_{i∈s} L_i(f_i(g a_i)) for all g, with L_i additive, a_i ∈ G and f_i smooth and left Γ-invariant, then the integral of F over Γ\\G is ∑_{i∈s} L_i(integral of f_i).")))))));
}
