using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Transference;

internal sealed class MassBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mass Basic", H("Mass Basic"),
        Blocks(
            Paragraph(Text("Trace dual of a unimodular hermitian lattice; short bases by transference. Effective bounded fundamental domain for a CM field in its adeles. Mahler-Godement compactness criterion for unitary groups; finite class number for definite spaces. Mass is positive; weighted count of norm-one vectors equals mass of rank one less.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Transference/MassBasic.classSum_card_norm_one_eq_mass"),
                H("classSum_card_norm_one_eq_mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For stably unramified E, the class sum for I_{j+1} at level K_0 of the number of vectors y in E^{j+1} with y*y = 1 and g⁻¹y integral equals mass_j.")))))));
}
