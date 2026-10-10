using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CycleSums;

internal sealed class ConsecutiveCycleSumsArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arithmetic for consecutive cycle completion: triangular totals, interval subset sums and the least usable core.",
        H("Triangular cores and interval subset sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("triangular-total"),
                DeclarationHandle.Create(Prefix + "tri"),
                H("Triangular total"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a natural number n, tri n is n times n plus one divided by two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("core-subset-sums"),
                DeclarationHandle.Create(Prefix + "subset_sums"),
                H("Subset sums cover the core interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least four, every integer s between two and tri k minus three is the sum of a finite subset of the labels two through k. Induction adjoins k plus one to cover a second interval; the two intervals overlap or abut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("least-triangular-core"),
                DeclarationHandle.Create(Prefix + "choose_core"),
                H("A short core with a quadratic edge budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least eight there exists k at least four and less than n with tri k at least n plus four and the square of k minus one strictly less than twice n plus eight. Choose the least qualifying k; its predecessor triangular total is less than n plus four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tail-total"),
                DeclarationHandle.Create(Prefix + "tail"),
                H("Tail-prefix total"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The tail total from core endpoint k to endpoint j sums the labels k plus one through j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-interval-cover"),
                DeclarationHandle.Create(Prefix + "interval_cover"),
                H("Tail translates cover every interior sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If k is at most n and tri k is at least n plus four, every q from three through tri n minus two belongs to an interval from three plus tail k j through tri k plus tail k j minus two for an endpoint j between k and n. Induction extends the endpoint; the next label is bounded by the core interval width, preventing gaps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-label-interval-sum"),
                DeclarationHandle.Create(Prefix + "sum_Icc_one"),
                H("Sum of all labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of labels one through n is tri n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("labels-without-hub-sum"),
                DeclarationHandle.Create(Prefix + "sum_Icc_two"),
                H("Sum excluding the hub label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least one, the sum of labels two through n is tri n minus one."))),
                DescribeRole.Theorem)),
        []));
}
