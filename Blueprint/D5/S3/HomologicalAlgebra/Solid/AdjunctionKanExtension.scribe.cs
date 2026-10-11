using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class AdjunctionKanExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "# The total left derived universal property from the actual derived adjunction The only additional premise is an actual adjunction to the protected exact derived inclusion. The geometric construction of that adjunction is separate. All complexes here are unbounded cochain complexes, and the localization is at every quasi-isomorphism.",
        H("Adjunction Kan Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-adjunctionkanextension-adjunction-isleftderivedfunctor"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/AdjunctionKanExtension.adjunction_isLeftDerivedFunctor"),
                H("adjunction is Left Derived Functor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal Mathlib property for all quasi-isomorphisms of unbounded complexes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-adjunctionkanextension-adjunction-hasleftderivedfunctor"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/AdjunctionKanExtension.adjunction_hasLeftDerivedFunctor"),
                H("adjunction has Left Derived Functor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Existence obtained from the constructed witness using Mathlib's `mk'`."))),
                DescribeRole.Theorem))));
}
