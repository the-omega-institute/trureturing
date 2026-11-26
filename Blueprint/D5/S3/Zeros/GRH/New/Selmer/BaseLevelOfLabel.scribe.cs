using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class BaseLevelOfLabelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Level Of Label", H("Base Level Of Label"),
        Blocks(
            Paragraph(Text("An auxiliary pair with apt labels c gives a BaseLevel of forms containing the image of the idempotent of c.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/BaseLevelOfLabel.exists_baseLevel"),
                H("exists_baseLevel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For apt c and auxiliary Q, some BaseLevel over the integers of ℚ̄_ℓ contains im e_c, with Mk·e_c preserving integrality (Mk = Data.chosenGroupOrder, e_c = tupleProj); its eigensystems at finite levels u off badPlaces D ℓ give normalised representations R that are IsLabelledColumn of one jump type, with (R − a)(R − 1) = 0 on inertia above Q ∪ Q̄, a the avatar of ϑ⁻¹.")))))));
}
