using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class HistoricalEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Historical isomorphism preserves the complete finite archive data and its signed readout.",
        H("Historical Equivalence of Rich Histories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("historical-isomorphism-data"),
                DeclarationHandle.Create(Prefix + "HistoricalIsoData"),
                H("Historical isomorphism extends an archive embedding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An isomorphism is a surjective archive embedding, hence an event bijection, "
                        + "preserving and reflecting causal order and all four absolute attributes. "
                        + "It also maps both current and selected regions exactly, for every dimension d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("historical-isomorphism-reflexivity"),
                DeclarationHandle.Create(Prefix + "historical_iso_refl"),
                H("Historical isomorphism is reflexive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity archive embedding preserves both distinguished regions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("historical-isomorphism-symmetry"),
                DeclarationHandle.Create(Prefix + "historical_iso_symm"),
                H("Historical isomorphism is symmetric"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inverting the event bijection reverses the isomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("historical-isomorphism-transitivity"),
                DeclarationHandle.Create(Prefix + "historical_iso_trans"),
                H("Historical isomorphism is transitive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Composition of archive embeddings preserves both region images."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("encoded-equality-gives-history-isomorphism"),
                DeclarationHandle.Create(Prefix + "encoded_equality_implies_historical"),
                H("Encoded equality gives historical isomorphism"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rich-code round trip is injective, so equal codes identify the same dependent "
                        + "rich object. Its identity archive embedding supplies the required isomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("historical-isomorphism-preserves-readout"),
                DeclarationHandle.Create(Prefix + "historical_iso_readout_eq"),
                H("Historical isomorphism preserves the signed readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected-image equality and finite-sum reindexing transport every contribution. "
                        + "Sign preservation, as part of the full attribute equality, makes the summands "
                        + "equal before reindexing.")),
                    Paragraph(Text(
                        "The parallel-versus-temporal nonisomorphism is intentionally left to the B2 "
                            + "worked-history specialization, which supplies those two causal relations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("historical-renaming-refutes-code-converse"),
                DeclarationHandle.Create(Prefix + "encoded_equality_converse_refuted"),
                H("A genuine HF renaming refutes the code converse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Singleton archives with different HF names have the same attributes, current image "
                        + "and empty selection, so renaming their sole event is a historical isomorphism. "
                        + "The witness works for every d with position Fin d to Int constantly zero. "
                        + "The closed converse claim quantifies over Rich 3, and its negation uses the "
                        + "dimension-three witness with HF names natCode 0 and natCode 1. Their literal "
                        + "rich codes differ. The separate numerical-converse example remains downstream."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Spacetime/ArchiveCarrier")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Spacetime/ArchiveEncoding")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ComplementCharge"))
        ]));
}
