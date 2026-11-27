using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Global;

internal sealed class ArtinReciprocityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Artin Reciprocity", H("Artin Reciprocity"),
        Blocks(
            Paragraph(Text("Artin reciprocity law on principal finite ideles, via cyclotomic characters; sign law.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Global/ArtinReciprocity.char_artinMap_principalIdele_eq_one_iff"),
                H("char_artinMap_principalIdele_eq_one_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Sign law: let K be a number field and χ a continuous character of its Galois group Γ non-trivial on every complex conjugation in Γ. Then for b in K^×, χ(Art b) is trivial exactly when the norm of b to ℚ is positive.")))))));
}
