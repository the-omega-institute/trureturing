using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeArithmetic;

internal sealed class IntegerExactDivisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact integer division selects the unique canonical integer quotient and has a strictly smaller domain.",
        H("Exact Integer Division"),
        Blocks(
            Paragraph(Text("Formula projection does not express the dependent archive carriers here. "
                + "The resolving Lean handles carry the typed statements; this narrative supplies no separate formula.")),
            Describe.Lean(
                DescribeId.Create("exact-guard"),
                DeclarationHandle.Create(Prefix + "exact_quotient_exists_unique"),
                H("Nonzero divisibility gives a unique integer quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ExactGuard requires a nonzero denominator readout and integer divisibility. Divisibility "
                        + "supplies the witness and nonzero multiplication cancellation proves uniqueness. Selection "
                        + "is defined only with this guard; no truncated division is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("literal-result"),
                DeclarationHandle.Create(Prefix + "exactDivide_literal"),
                H("The output is the literal integer representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the unique integer k satisfying numerator readout equal to k times denominator "
                        + "readout, exactDivide returns representative d k as its underlying rich history. The "
                        + "balanced readout is k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-fraction"),
                DeclarationHandle.Create(Prefix + "exact_guard_iff_integer_value"),
                H("The exact guard is equivalent to an integral fraction value"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A legal rich fraction satisfies the exact guard precisely when its rational readout is an "
                        + "integer cast. This also makes the guard invariant under fraction equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotient-agreement"),
                DeclarationHandle.Create(Prefix + "quotient_exactDivide"),
                H("Retaining the pair and selecting the integer have equal quotient value"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original unquotiented fraction pair retains both input histories. "
                        + "Its quotient class equals the class of the integer embedding of the selected canonical output."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("archive-loss"),
                DeclarationHandle.Create(Prefix + "exactDivide_loses_product_history"),
                H("Canonical selection loses generated input history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every dimension and integer n, multiply its canonical balanced history by the "
                        + "canonical history of one, then divide exactly by one. The output is canonical and differs "
                        + "from the input product history: the actual product archive has strictly more events. Only "
                        + "arbitrary-d producer APIs are used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("domain-refutation"),
                DeclarationHandle.Create(Prefix + "division_domains_equal_refuted"),
                H("The half pair refutes equality of the two domains"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent closed claim states that integer exact division and guarded rational "
                        + "division of embedded integers have equal domains at dimension three. The actual half pair "
                        + "has nonzero denominator two; two does not divide one. The theorem proves the negation of "
                        + "that claim, without an unrelated conjunct."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient"))
        ]));
}
