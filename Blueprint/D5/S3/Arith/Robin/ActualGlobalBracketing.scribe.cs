using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualGlobalBracketingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualGlobalBracketing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every integer is bracketed at one positive price by the complete original strict and maximal optimizers.",
        H("Actual global bracketing"),
        Blocks(
            Paragraph(Text("Strict and maximal products keep their distinct tie conventions. Activation finiteness, a usable positive seed and coverage are proved rather than assumed as finiteness, growth or cofinality premises.")),
            Describe.Lean(
                DescribeId.Create("actual-next-event-product"),
                DeclarationHandle.Create(Prefix + "next_event_product"),
                H("The entire product at the next activation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Above a positive seed, if strictInteger(q)>1, the least activation value r>q has maximalInteger(r)=strictInteger(q). Every prime factorization entry is identified, including all simultaneous ties. The equality concerns the entire integer, not a prefix or one-prime update."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-all-integer-bracketing"),
                DeclarationHandle.Create(Prefix + "all_integer_bracketing"),
                H("A positive-price bracket for every integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n>=2 there is a positive real q with strictInteger(q)<=n<=maximalInteger(q). The nth two-adic marginal gives a seed whose maximal product is at least n. Choose the greatest qualifying activation value. If its strict product exceeded n, the next-event identity would give a greater qualifying activation, a contradiction. No optimizer-existence, inventory-growth or coverage premise remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-coverage-above-5040"),
                DeclarationHandle.Create(Prefix + "coverage_above_5040"),
                H("Retain the original 5040 boundary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every n>5040 is either at most boundaryCap, the maximal product in the constructed 5041 bracket, or lies in a same-price interval whose strict endpoint already exceeds 5040. Cross-price divisibility places every interval crossing 5040 in that finite region. The Robin interval consumer separately identifies and pays this finite boundary and keeps the analytic endpoint estimates explicit."))),
                DescribeRole.Theorem))));
}
