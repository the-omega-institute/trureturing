using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeExpressions;

internal sealed class IntegerExpressionCompatibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expressions on actual balanced integer histories.",
        H("Expressions on actual balanced integer histories"),
        Blocks(
            Paragraph(Text("Typed Lean handles carry these statements. Formula projection limitations are "
                + "reported by the canonical Scribe tools; no handwritten formula substitutes for a Lean type. "
                + "The actual real interpretation and the full shared-world expression theorem remain E2.")),
            Describe.Lean(
                DescribeId.Create("division"),
                DeclarationHandle.Create(Prefix + "exactQuotient_eq_div"),
                H("The exact quotient equals ordinary integer division on its domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The domain requires a nonzero divisor and divisibility. "
                    + "IntegerExactDivision.exactQuotient_unique and Int.ediv_mul_cancel identify "
                    + "the two quotients on that domain; one divided by two stays illegal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout"),
                DeclarationHandle.Create(Prefix + "readout_eval"),
                H("Readout commutes with every finite native expression"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Constants use balancedSection and variables range over all BalancedRich d. "
                    + "The operations are complementBalanced, parallelBalanced, productBalanced and "
                    + "guarded exactDivide. The theorem includes both successful results and "
                    + "failure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("guards"),
                DeclarationHandle.Create(Prefix + "legal_iff_all_nodes"),
                H("Rich legality equals all ordinary node guards"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The generic structural legality theorem retains both children and each "
                    + "nonzero-and-divisibility guard. This holds for every finite term and every "
                    + "assignment, in particular dimension three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("value"),
                DeclarationHandle.Create(Prefix + "value_eq"),
                H("Legal rich and ordinary results have equal values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conditional value identity follows from full Option commutation. "
                    + "Ordinary evaluation itself remains partial at every division."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equality"),
                DeclarationHandle.Create(Prefix + "value_eq_iff_class_eq"),
                H("Ordinary value equality is actual integer quotient equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "IntegerQuotient.class_eq_iff identifies the result classes. This does not "
                    + "identify the raw archived histories."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Rewriting/Expressions/GuardedArithmeticTerms")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient"))
        ]));
}
