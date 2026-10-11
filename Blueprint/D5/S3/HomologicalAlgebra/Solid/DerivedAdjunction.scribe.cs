using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedAdjunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supporting results for the unbounded derived adjunction. These do not assume existence of derived solidification or import the upstream derived gaps.",
        H("Derived Adjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedadjunction-map-iskprojective-of-exact-rightadjoint"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedAdjunction.map_isKProjective_of_exact_rightAdjoint"),
                H("map is KProjective of exact right Adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The left adjoint of an exact additive functor sends unbounded K-projective complexes to K-projective complexes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedadjunction-reflection-map-iskprojective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedAdjunction.reflection_map_isKProjective"),
                H("reflection map is KProjective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual protected reflector preserves K-projectivity. This result asserts no existence of replacements for general light condensed complexes."))),
                DescribeRole.Theorem))));
}
