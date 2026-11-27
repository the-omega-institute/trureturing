using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Unramified;

internal sealed class SphericalHeckeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spherical Hecke", H("Spherical Hecke"),
        Blocks(
            Paragraph(Text("Spherical Hecke operators at split places commute, are adjoint, and are simultaneously diagonalisable. Weights, Hecke polynomials, eigenforms, labels and expected Hodge-Tate jumps. Hecke polynomial at a split place, as operator; spherical eigenvectors. Lifts of finite reductions to K; action of normalising finite group on level vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Unramified/SphericalHecke.exists_heckeSplit_eq_smul"),
                H("exists_heckeSplit_eq_smul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("At a split place w, for every p there are scalars t_i such that each vector y with Hecke eigensystem p at w satisfies T_{w,i} y = t_i y for all i.")))))));
}
