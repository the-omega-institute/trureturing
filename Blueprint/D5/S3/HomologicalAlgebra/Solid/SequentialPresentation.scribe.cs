using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class SequentialPresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable telescope presentations in an AB5 abelian category. New proofs, released under the Apache 2.0 license.",
        H("Sequential Presentation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-sequentialpresentation-sequenceprojection-jointly-monic"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SequentialPresentation.sequenceProjection_jointly_monic"),
                H("sequence Projection jointly monic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("AB5 makes the canonical map from the sum into the product monic. This is proved by taking the filtered union of its finite split submaps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-sequentialpresentation-oneminussequence-mono"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SequentialPresentation.oneMinusSequence_mono"),
                H("one Minus Sequence mono"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One minus the forward transition is monic for every countable sequence; no monicity of the transitions is required."))),
                DescribeRole.Theorem))));
}
