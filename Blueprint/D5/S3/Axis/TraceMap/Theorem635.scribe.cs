using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis.TraceMap;

internal sealed class Theorem635Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var K = Id("K");

        var defs = Equal(
            Call("W", K),
            Call("sum", Call("range", Call("fib", Add(K, Num(1)))), Call("wordWeight")));

        var recurrence = Equal(
            Call("W", Add(K, Num(2))),
            Add(Call("W", Add(K, Num(1))),
                Multiply(Call("t", Add(K, Num(2))), Call("W", K))));

        var orbit = Equal(
            Call("F", Call("state", K)),
            Call("state", Add(K, Num(1))));

        var whole = new Formula.Logic(
            defs,
            FormulaLogicOperator.And,
            new Formula.Logic(recurrence, FormulaLogicOperator.And, orbit));

        const string declarationPrefix = "D5/S3/Axis/TraceMap/Theorem635.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The three clauses of the axis trace map theorem hold of one pair of sequences.",
            H("Theorem 635"),
            Blocks(
                Paragraph(Text(
                    "The theorem was carved into three clauses: the two objects and the bridge "
                        + "that makes the summation bound mean bounded depth, the pair of "
                        + "recurrences those objects satisfy, and the four coordinate map whose "
                        + "orbit carries the axis state.")),
                Paragraph(Text(
                    "Each clause was proved on its own and none is restated. What this adds is "
                        + "that the three hold of one pair of sequences at once. Read "
                        + "separately, a reader has to check by eye that the objects the first "
                        + "clause defines are the ones the second runs recurrences on, and that "
                        + "the state the third iterates is built from those same two sequences. "
                        + "Assembled, that is a proof term instead.")),
                Paragraph(Text(
                    "Replacing the second reading by a copy of the first in the third block "
                        + "makes the module fail to build, so the shared parameters carry "
                        + "weight rather than appearing to. The convergence the source records "
                        + "at the end of the third clause rests on a numerical certificate "
                        + "rather than an argument, and is not claimed.")),
                Describe.Lean(
                    DescribeId.Create("the-three-clauses-assembled"),
                    DeclarationHandle.Create(declarationPrefix + "axis_trace_map_theorem"),
                    H("The three clauses assembled"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(whole)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "One conjunction over the same two parameters, carrying the definitions "
                            + "and their bridge, the pair of recurrences, and the map with its "
                            + "orbit."))),
                    DescribeRole.Theorem))));
    }
}
