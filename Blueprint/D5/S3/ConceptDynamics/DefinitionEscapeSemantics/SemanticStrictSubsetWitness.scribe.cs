using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSemantics;

internal sealed class SemanticStrictSubsetWitnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeSemantics/"
            + "SemanticStrictSubsetWitness."
            + "semantic_strict_subset_has_new_only_witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic strict expansion contains a witness in the directed new-domain difference.",
        H("Semantic Strict-Expansion Witness"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-strict-subset-new-only-witness"),
            DeclarationHandle.Create(Declaration),
            H("Strict expansion supplies a new-domain-difference witness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The transport frame interprets domain membership directly. "
                        + "SemanticNewOnly(S,z,J,J') means that z belongs to J' and does "
                        + "not belong to J; it is not an independent black-box predicate.")),
                Paragraph(Text(
                    "SemanticStrictSubset(S,J,J') is exactly preservation of membership "
                        + "from J to J' together with existence of a SemanticNewOnly point. "
                        + "The theorem projects that second conjunct without finiteness, "
                        + "inhabitance, decidable equality, or result-uniqueness assumptions.")),
                Paragraph(Text(
                    "This discharges obligation 57.3-A from definition-escape-completion-theory "
                        + "atom generic-residual-e8b7049497c6cf0d8b563c5d37805dc2ba0370dd790914"
                        + "983f40359f8fe2d05e. The later certificate and overreach obligations "
                        + "remain separate claims."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula frame = F.Id("S");
        Formula oldDomain = F.Id("J");
        Formula newDomain = Seq(F.Id("J"), Apos);
        Formula evidence = F.Id("z");

        return Disp(Seq(
            Call("SemanticStrictSubset", frame, oldDomain, newDomain),
            Sp, Rightarrow, Sp,
            Exists, Sp, evidence, Comma, Sp,
            Call("SemanticNewOnly", frame, evidence, oldDomain, newDomain),
            Dot));
    }
}
