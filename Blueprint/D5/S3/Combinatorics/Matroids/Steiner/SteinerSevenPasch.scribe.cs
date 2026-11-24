using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids.Steiner;

internal sealed class SteinerSevenPaschDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/Steiner/SteinerSevenPasch";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven Pasches in a centreless Steiner loop can obstruct every two-dimensional labelling.",
        H("A seven-Pasch counterexample in fibre dimension two"),
        Blocks(Describe.Lean(
            DescribeId.Create("steiner-seven-pasch-counterexample"),
            DeclarationHandle.Create(Module + ".result"),
            H("Seven Pasches can prevent a common maximum"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A 19-point Steiner triple system gives a twenty-element centreless Steiner loop. Its seven Pasches are exactly the Pasches of an embedded Fano plane. The multiplication and block-incidence tables determine the Steiner laws, the trivial centre, and the complete list of unordered Pasches.")),
                Paragraph(Text("For each normalized label table into a binary fibre of dimension two, take three generating Pasch returns. The seven returns consist of the three generators, their three pairwise sums and their triple sum. Some nonempty sum of the three is zero in dimension two. The corresponding outside square misses successful starts. The fixed-pair return construction yields a second table with a strictly larger count for that pair."))),
            DescribeRole.Theorem))));
}

