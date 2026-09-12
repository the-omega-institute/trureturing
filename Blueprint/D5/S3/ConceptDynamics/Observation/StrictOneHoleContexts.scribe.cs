using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Observation;

internal sealed class StrictOneHoleContextsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All finite strict one-hole observations determine the greatest strong congruence below the readout kernel.",
        H("Strict One-Hole Contexts"),
        Blocks(
            Paragraph(Text(
                "The state carrier, symbol set and readout codomain are arbitrary. Each symbol has a finite arity, "
                    + "possibly zero, and an Option-valued operation. An arbitrary domain with a function on its "
                    + "subtype gives exactly such a partial operation by the classical Part/Option equivalence. "
                    + "None means outside the domain; some x records the actual output x. Composition uses bind "
                    + "and propagates failure strictly.")),
            Paragraph(Text(
                "A generator chooses a symbol, one of its slots, and exactly one parameter for every other slot. "
                    + "All state values are allowed as parameters. No default state is needed, and a nullary "
                    + "symbol has no generator. Contexts are the range of the denotation of finite generator words "
                    + "as partial functions; the empty word denotes the identity. A successful readout is tagged "
                    + "with some and remains distinct from none even when the readout has a failure-like value.")),
            Describe.Lean(
                DescribeId.Create("semantic-contexts-and-words"),
                DeclarationHandle.Create(Prefix + "forall_contexts_iff_words"),
                H("Semantic contexts and finite words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality of observations for every function in the semantic context family is equivalent "
                        + "to equality for every finite generator word. Different words may denote the same function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greatest-strong-congruence"),
                DeclarationHandle.Create(Prefix + "contextual_equivalence_is_greatest"),
                H("The greatest strong domain-preserving congruence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Contextual equivalence is a strong congruence, lies in the kernel of the readout, and contains "
                        + "every strong congruence lying in that kernel. Strong congruence means that coordinatewise "
                        + "related tuples belong to the operation domain simultaneously and have related outputs "
                        + "when defined. Replacing coordinates one at a time uses every slot and the actual fixed "
                        + "parameters at that step. For greatestness, Option of the candidate quotient records "
                        + "both failure and the output class; the readout factors through that quotient. No "
                        + "inhabitedness or surjectivity hypothesis is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signature-extension-refines"),
                DeclarationHandle.Create(Prefix + "signature_extension_refines"),
                H("Extending the signature refines equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An extension embeds the old symbols, preserves each old arity, and preserves the entire "
                        + "Option-valued operation after arity transport. Thus both its domain and every normal "
                        + "value are unchanged. Contextual equivalence for the extended signature is contained "
                        + "in contextual equivalence for the original signature."))),
                DescribeRole.Theorem))));
}
