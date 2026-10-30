using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class FibonacciIncidenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/FibonacciIncidence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport finite Fibonacci substitution words through their incidence matrix and additive observables.",
        H("Incidence Dynamics of Fibonacci Substitution Words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parikh-vector"),
                DeclarationHandle.Create(Prefix + "parikh"),
                H("The Boolean Parikh vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite Boolean word, parikh records the number of occurrences of each "
                        + "Boolean letter as a function on the alphabet."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("substitution"),
                DeclarationHandle.Create(Prefix + "substitute"),
                H("One Fibonacci substitution step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite-word substitution maps each letter by the Fibonacci substitution "
                        + "and concatenates the resulting images."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("iteration"),
                DeclarationHandle.Create(Prefix + "iterate"),
                H("Iterated substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "iterate n w applies the substitution n times, with the zeroth iterate equal "
                        + "to w."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("incidence-matrix"),
                DeclarationHandle.Create(Prefix + "incidence"),
                H("The substitution incidence matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The matrix entry in output row b and input column a is the number of b letters "
                        + "in the substitution image of a."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-sum"),
                DeclarationHandle.Create(Prefix + "weightedSum"),
                H("An additive letter observable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "weightedSum assigns a value to each letter and sums those values along a finite "
                        + "word in an arbitrary additive commutative monoid."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parikh-substitute"),
                DeclarationHandle.Create(Prefix + "parikh_substitute"),
                H("Substitution acts by the incidence matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite Boolean word, its Parikh vector after one substitution is "
                        + "the incidence matrix multiplied by its original Parikh vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parikh-iterate"),
                DeclarationHandle.Create(Prefix + "parikh_iterate"),
                H("Iterated substitution acts by matrix powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After n substitution steps, the Parikh vector is obtained by applying the nth "
                        + "power of the incidence matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-parikh"),
                DeclarationHandle.Create(Prefix + "weightedSum_eq_parikh"),
                H("Additive observables factor through Parikh counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every additive weighted sum equals the finite sum of each letter's weight "
                        + "scaled by its Parikh count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-iterate"),
                DeclarationHandle.Create(Prefix + "weighted_iterate"),
                H("Weighted observables under iterated substitution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Combining the two transport laws expresses any weighted observable after n "
                        + "iterations using the incidence-matrix power and the initial Parikh vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fib-word-iterate"),
                DeclarationHandle.Create(Prefix + "fibWord_eq_iterate"),
                H("Finite Fibonacci words are substitution iterates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository's finite Fibonacci word at level n is the nth substitution "
                        + "iterate of the one-letter true seed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fib-word-parikh"),
                DeclarationHandle.Create(Prefix + "fibWord_parikh"),
                H("Exact letter counts in finite Fibonacci words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At level n, the true letter occurs Nat.fib (n+1) times and the false letter "
                        + "occurs Nat.fib n times."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/GoldenGapPrefix"))]));
}
