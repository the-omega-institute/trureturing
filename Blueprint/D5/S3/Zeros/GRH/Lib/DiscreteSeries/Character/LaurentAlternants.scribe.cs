using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character;

internal sealed class LaurentAlternantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laurent Alternants", H("Laurent Alternants"),
        Blocks(
            Paragraph(Text("Laurent polynomials on the torus, Weyl denominators, alternants, leading monomials, density.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/LaurentAlternants.apply_comp_perm_of_conj_invariant"),
                H("apply_comp_perm_of_conj_invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If f on the diagonal torus and d on K satisfy d(yxy⁻¹) = f(x) for all y in K and x in the torus, then f is invariant under every permutation w of the coordinates that preserves the signs ε.")))))));
}
