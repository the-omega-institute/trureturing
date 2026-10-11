using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. Realization in the protected D(Solid) of every object of the actual derived-local category. The concrete free-generator kernel resolution, finite layers, lower telescope and good upper telescope supply the unbounded essential-image argument. Neither solid homology nor the ordinary reflection is treated as a realization theorem. Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1 and Lemma 3.3.2.",
        H("Derived Realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedrealization-derivedlocalreflection-realized-complex"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedRealization.derivedLocalReflection_realized_complex"),
                H("derived Local Reflection realized complex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every arbitrary unbounded ambient complex has its actual derived-local reflection in the essential image of the protected derived inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedrealization-derivedinclusiontolocal-esssurj"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedRealization.derivedInclusionToLocal_essSurj"),
                H("derived Inclusion To Local ess Surj"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual unbounded realization theorem, with no generation, full-faithfulness or realization premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedrealization-derivedsolidlocalequivalence"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedRealization.derivedSolidLocalEquivalence"),
                H("derived Solid Local Equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine equivalence preserves the exact protected inclusion."))),
                DescribeRole.Definition))));
}
