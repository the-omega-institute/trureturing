using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms;

internal sealed class AdaptedHomDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adapted Hom", H("Adapted Hom"),
        Blocks(
            Paragraph(Text("Adelic Iwasawa decomposition for unitary parabolics; centre of radical and Fourier coefficients. Fourier coefficients of automorphic functions along centre of a radical: basic laws, inversion. Radical of a line stabiliser: modulus on hermitian matrices, cocompact rational points. Adapted splittings pass to Hom spaces; slices there written in Kronecker frames.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/AdaptedHom.exists_isCompact_rat_mul_radicalElt_mem"),
                H("exists_isCompact_rat_mul_radicalElt_mem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a splitting of V' over V along an isotropic line, the radical is cocompact modulo its rational points: some compact set K has n(y,z)·n(c,b) ∈ K for every n(c,b) and a suitable rational n(y,z), with n = Space.Splitting.radicalElt.")))))));
}
