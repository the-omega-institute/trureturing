using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Poincare;

internal sealed class BesselSubgroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Subgroup", H("Bessel Subgroup"),
        Blocks(
            Paragraph(Text("Bessel subgroup S=UH of a unitary group: normality, factorisation, additive simple-root character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Poincare/BesselSubgroup.simpleRootSum"),
                H("simpleRootSum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For s in the unitary group, the sum σ(s) of the entries just above the diagonal of the block of s on the frame indices e₁,…,e_ϱ,z.")))))));
}
