using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeExpressions;

internal sealed class RationalExpressionCompatibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expressions on actual rich rational fractions.",
        H("Expressions on actual rich rational fractions"),
        Blocks(
            Paragraph(Text("Typed Lean handles carry these statements. Formula projection limitations are "
                + "reported by the canonical Scribe tools; no handwritten formula substitutes for a Lean type. "
                + "The actual real interpretation and the full shared-world expression theorem remain E2.")),
            Describe.Lean(
                DescribeId.Create("division"),
                DeclarationHandle.Create(Prefix + "guard_iff"),
                H("The native divisor guard is precisely nonzero readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RichRational.division_guard_iff proves this on the actual Fraction d "
                    + "carrier. RichRational.div consumes the proof and constructs a fraction with "
                    + "a nonzero denominator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout"),
                DeclarationHandle.Create(Prefix + "readout_eval"),
                H("Readout commutes with every finite native rational expression"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Constants use rationalSection and variables range over actual "
                    + "RichRational.Fraction d. The implementation uses exactly RichRational.add, "
                    + "mul, neg and guarded div with their established readout laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("guards"),
                DeclarationHandle.Create(Prefix + "legal_iff_all_nodes"),
                H("Every intermediate rational division remains guarded"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AllLegal retains every child and each nonzero divisor readout. Rat division "
                    + "being total at zero does not make the partial ordinary expression evaluator "
                    + "total."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("value"),
                DeclarationHandle.Create(Prefix + "value_eq"),
                H("Legal rich and ordinary rational results have equal values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source value identity follows from equality of the full Option "
                    + "evaluations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equality"),
                DeclarationHandle.Create(Prefix + "value_eq_iff_class_eq"),
                H("Ordinary equality is actual rational quotient equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof combines RichRational.cross_iff_readout with "
                    + "RationalQuotient.class_eq_iff on the evaluated native fractions."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Rewriting/Expressions/GuardedArithmeticTerms")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient"))
        ]));
}
