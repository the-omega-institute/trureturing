using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Reduction;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Defs", H("Defs"),
        Blocks(
            Paragraph(Text("Haar measure on the adelic unitary group and on its automorphic quotient. Finite covolume of unitary groups and Weil's convergence criterion for 2t < n. Automorphic functions, forms of a type, Petersson product, theta kernels, right convolution at infinity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Reduction/Defs.eq_zero_of_petersson_self"),
                H("eq_zero_of_petersson_self"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Petersson product is definite: an automorphic function F that is square integrable on Γ\\G and has ⟨F, F⟩ = 0 vanishes everywhere.")))))));
}
