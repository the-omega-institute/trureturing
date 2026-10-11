using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ConeColimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coproducts of the actual mapping cones used by the unbounded cellular construction. New proofs, released under the Apache 2.0 license.",
        H("Cone Colimit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-conecolimit-complexdiagramasfunctoriso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ConeColimit.complexDiagramAsFunctorIso"),
                H("complex Diagram As Functor Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transposing the existing complex-to-diagram construction returns the original unbounded complex, with its original differentials."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-conecolimit-mappingconecoproductiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ConeColimit.mappingConeCoproductIso"),
                H("mapping Cone Coproduct Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arbitrary coproducts of mapping cones are the mapping cone of the actual coproduct map. The complexes need not be bounded."))),
                DescribeRole.Definition))));
}
