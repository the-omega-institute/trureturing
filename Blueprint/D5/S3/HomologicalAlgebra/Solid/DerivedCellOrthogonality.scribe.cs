using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedCellOrthogonalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The protected defining cells tested in the actual unbounded derived category. These proofs use only the exact tensor/internal-Hom adjunction for P, not a derived solidification adjunction. New proofs, Apache 2.0.",
        H("Derived Cell Orthogonality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedcellorthogonality-solidlocalizationcell-derivedinclusionhom-zero"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidLocalizationCell_derivedInclusionHom_zero"),
                H("solid Localization Cell derived Inclusion Hom zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In particular, the actual defining cells have zero derived maps into the image of every unbounded solid complex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedcellorthogonality-solidcellattachment-derivedprecomp-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality.solidCellAttachment_derivedPrecomp_bijective"),
                H("solid Cell Attachment derived Precomp bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual attachment along one defining cell has a universal derived comparison against every derived-local target. This supplies both existence and uniqueness for derived maps (not only chain-map homotopies)."))),
                DescribeRole.Theorem))));
}
