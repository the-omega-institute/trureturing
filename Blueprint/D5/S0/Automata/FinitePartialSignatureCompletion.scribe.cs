using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class FinitePartialSignatureCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/FinitePartialSignatureCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For normalized finite partial-signature requirements over nonempty output and return "
            + "types, the minimum completion size is the full-pair count plus the larger residual count.",
        H("Finite Partial-Signature Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("requirements"),
                DeclarationHandle.Create(Prefix + "Requirements"),
                H("Normalized partial-signature requirements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For output, return-class, full-pair, output-only, and return-only types in "
                    + "one universe, Requirements stores embeddings of full indices into output-return "
                    + "pairs and of residual indices into their respective coordinate types. Every "
                    + "residual output differs from every full pair's output, and every residual "
                    + "return differs from every full pair's return. The structure itself assumes "
                    + "neither finiteness nor nonemptiness of these types."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("required-signature-count"),
                DeclarationHandle.Create(Prefix + "requiredSignatureCount"),
                H("The required signature count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For normalized requirements with finite Full, OutputOnly, and ReturnOnly "
                    + "index types, requiredSignatureCount is the cardinality of Full plus the "
                    + "maximum of the cardinalities of OutputOnly and ReturnOnly. This definition "
                    + "depends only on those three cardinalities and does not assume that the "
                    + "output or return-class type is nonempty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("completion"),
                DeclarationHandle.Create(Prefix + "Completion"),
                H("A finite injective completion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For normalized requirements, a Completion supplies a state type in the same "
                    + "universe, a Fintype instance on it, and an embedding of states into "
                    + "output-return pairs. Its three witness maps realize every full pair exactly, "
                    + "every residual output in the first coordinate, and every residual return in "
                    + "the second coordinate. Injectivity of the witness maps is not a separate "
                    + "field, and the structure does not require every state to be a witness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-optimal-completion"),
                DeclarationHandle.Create(Prefix + "exists_optimal_completion"),
                H("An optimal completion exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For normalized requirements with finite Full, OutputOnly, and ReturnOnly "
                    + "index types and with both Output and Class nonempty, there exists a "
                    + "completion whose state cardinality equals requiredSignatureCount. The "
                    + "construction retains every full pair, pairs residual requirements by "
                    + "finite indices, and fills unmatched coordinates with chosen defaults; "
                    + "it does not assert uniqueness of the resulting completion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-partial-signature-completion-exact"),
                DeclarationHandle.Create(Prefix + "finite_partial_signature_completion_exact"),
                H("The exact minimum completion size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For normalized requirements with all three index types finite and with "
                    + "nonempty output and return-class types, requiredSignatureCount is a lower "
                    + "bound for the state cardinality of every completion and is attained by "
                    + "some completion. Thus the full-pair count plus the maximum of the two "
                    + "fresh residual counts is the exact minimum under these hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("output-projection"),
                DeclarationHandle.Create(Prefix + "outputProjection"),
                H("Outputs present in full signatures"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set of output-return pairs and decidable equality on Output, "
                    + "outputProjection is its finite-set image under the first-coordinate map. "
                    + "It contains precisely the outputs occurring in the full signatures, "
                    + "with repeated output values represented only once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("return-projection"),
                DeclarationHandle.Create(Prefix + "returnProjection"),
                H("Returns present in full signatures"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite set of output-return pairs and decidable equality on Class, "
                    + "returnProjection is its finite-set image under the second-coordinate map. "
                    + "It contains precisely the return classes occurring in the full signatures, "
                    + "with duplicate return values removed by the finite-set image."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residual-outputs"),
                DeclarationHandle.Create(Prefix + "residualOutputs"),
                H("Uncovered output requirements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given a finite set of full signatures, a finite set of required outputs, "
                    + "and decidable equality on Output, residualOutputs is the required output "
                    + "set minus outputProjection of the full signatures. It retains exactly "
                    + "those requested outputs that do not already occur in a full pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residual-returns"),
                DeclarationHandle.Create(Prefix + "residualReturns"),
                H("Uncovered return requirements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given a finite set of full signatures, a finite set of required return "
                    + "classes, and decidable equality on Class, residualReturns is the required "
                    + "return set minus returnProjection of the full signatures. It retains "
                    + "exactly the requested returns not already covered by a full pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("requirements-of-finsets"),
                DeclarationHandle.Create(Prefix + "requirementsOfFinsets"),
                H("Normalize finite-set requirements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For output and return-class types with decidable equality, finite sets of "
                    + "full signatures, requested outputs, and requested returns determine "
                    + "normalized Requirements. The index types are the subtypes of the full "
                    + "set and the two residual sets, and all three embeddings are subtype "
                    + "inclusions. Removing the full projections ensures the required freshness; "
                    + "neither coordinate type must be nonempty for this normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("required-signature-count-requirements-of-finsets"),
                DeclarationHandle.Create(Prefix + "requiredSignatureCount_requirementsOfFinsets"),
                H("The finite-set count formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite sets of full signatures, required outputs, and required returns "
                    + "over coordinate types with decidable equality, requiredSignatureCount of "
                    + "requirementsOfFinsets equals the full set's cardinality plus the maximum "
                    + "of the cardinalities of residualOutputs and residualReturns. This is an "
                    + "identity of counts and requires no nonemptiness assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-partial-signature-completion-finsets"),
                DeclarationHandle.Create(Prefix + "finite_partial_signature_completion_finsets"),
                H("The exact minimum for finite-set requirements"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonempty Output and Class types with decidable equality, let the "
                    + "normalized requirements come from any finite sets of full signatures, "
                    + "requested outputs, and requested returns. Every completion of these "
                    + "requirements has at least the full set's cardinality plus the maximum "
                    + "of the two residual-set cardinalities states, and some completion has "
                    + "exactly that many. Residuals remove values already in the full projections; "
                    + "the ambient coordinate types need not be finite."))),
                DescribeRole.Theorem))));
}
