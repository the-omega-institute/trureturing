using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class PureAdditivePrimeHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure Additive Prime Histories.",
        H("Pure Additive Prime Histories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pureadditiveprimehistory-pure-additive-run"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.pure_additive_run"),
                H("Additive evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A word consisting only of additive prime letters adds the sum of its labels "
                    + "to any natural initial state. Starting at zero gives the prime sum itself; "
                    + "starting at one increases that endpoint by exactly one. "
                    + "The empty word leaves the initial state unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pureadditiveprimehistory-additive-tuple-count"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory.additive_tuple_count"),
                H("Ordered tuple counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An ordered tuple of k primes at most X gives a word by making every label "
                    + "an additive letter. Repeated primes are allowed, and the word uniquely "
                    + "determines the tuple. The words ending at the natural number N from "
                    + "initial state one therefore correspond bijectively to tuples with "
                    + "integer sum N minus one. This includes length zero and empty prime sets."))),
                DescribeRole.Theorem))));
}
