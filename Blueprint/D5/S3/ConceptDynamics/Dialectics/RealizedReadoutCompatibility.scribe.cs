using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class RealizedReadoutCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("q");
        var equality = Equal(
            Call("realizedReadout", q),
            Call("rangeFactorization", q));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The realized readout is Mathlib's canonical factorization through a range.",
            H("Realized Readout Compatibility"),
            Blocks(
                Paragraph(Text(
                    "For every function q from a state type X to a codomain B, the local "
                        + "realized readout is equal as a function to Mathlib's "
                        + "Set.rangeFactorization q.")),
                Paragraph(Text(
                    "This equality does not say that q is injective or surjective onto B, "
                        + "and it does not identify B with the realized range. Both sides "
                        + "already have codomain Set.range q, so no quotient or coercion is "
                        + "introduced.")),
                Describe.Lean(
                    DescribeId.Create("realized-readout-is-range-factorization"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/Dialectics/"
                            + "RealizedReadoutCompatibility."
                            + "realizedReadout_eq_rangeFactorization"),
                    H("The realized readout is range factorization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(equality)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The pinned upstream and local definitions construct the same "
                            + "subtype-valued function; their range-membership proofs are "
                            + "proof-irrelevant."))),
                    DescribeRole.Theorem))));
    }
}
