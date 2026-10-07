using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DerivedCoproductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual coproducts in the unbounded derived category of an abelian category with exact sums. This supplies the sum comparison needed by the cellular telescope; no derived solidification is assumed. New proofs, released under the Apache 2.0 license.",
        H("Derived Coproduct"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-derivedcoproduct-derivedq-preservescoproduct"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.derivedQ_preservesCoproduct"),
                H("derived Q preserves Coproduct"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The official unbounded derived localization preserves the actual coproduct of complexes whenever sums in the original category are exact. This follows from the proved roof argument, not an assumed property of Q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-derivedcoproduct-lightcondensedderivedq-preservescoproduct"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct.lightCondensedDerivedQ_preservesCoproduct"),
                H("light Condensed Derived Q preserves Coproduct"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum theorem applies to the actual protected light condensed category and every small family of unbounded complexes."))),
                DescribeRole.Theorem))));
}
