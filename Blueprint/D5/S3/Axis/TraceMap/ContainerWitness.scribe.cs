using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis.TraceMap;

internal sealed class ContainerWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var K = Id("K");
        var J = Id("J");

        var parent = Equal(
            Call("tracePartial", Add(K, Num(2))),
            Add(Call("tracePartial", Add(K, Num(1))),
                Multiply(Call("tA", Add(K, Num(2))), Call("tracePartial", K))));

        var coherence = Equal(
            Call("tracePartial", J),
            Call("axisPartialSum", Add(J, Num(1))));

        var child = Equal(
            Call("axisPartialSum", Add(J, Num(2))),
            Add(Call("axisPartialSum", Add(J, Num(1))),
                Multiply(Call("tB", Add(J, Num(2))), Call("axisPartialSum", J))));

        var whole = new Formula.Logic(
            parent,
            FormulaLogicOperator.And,
            new Formula.Logic(coherence, FormulaLogicOperator.And, child));

        const string declarationPrefix = "D5/S3/Axis/TraceMap/ContainerWitness.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "One statement naming the parent receipt's carrier and the whole child package.",
            H("Container Witness"),
            Blocks(
                Paragraph(Text(
                    "The container atom carries a pre-committed receipt naming one carrier, "
                        + "while its three clause atoms are covered by declarations written "
                        + "eight days later under a different index convention. Covering the "
                        + "parent against a carrier its children do not use would certify an "
                        + "equivalence nobody had proved.")),
                Paragraph(Text(
                    "This statement names both sides at once: the recurrence pair the parent's "
                        + "own carrier proves at the substituted readings, the coherence "
                        + "relation carrying that carrier onto the one the children use, and "
                        + "the child recurrence itself. Each conjunct is an existing theorem "
                        + "applied; none is restated.")),
                Paragraph(Text(
                    "What the conjunction adds is that they hold of one pair of readings at "
                        + "once. Removing the substitution from the parent conjunct makes the "
                        + "module fail to build, so the three blocks are bound together rather "
                        + "than merely adjacent.")),
                Describe.Lean(
                    DescribeId.Create("the-parent-carrier-and-the-child-package-together"),
                    DeclarationHandle.Create(declarationPrefix + "container_witness"),
                    H("The parent carrier and the child package together"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(whole)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A necessary condition for settling the container, not a sufficient "
                            + "one: which index convention the source text intends remains "
                            + "unmeasured, and that is what would decide whether either "
                            + "carrier is faithful to it."))),
                    DescribeRole.Theorem))));
    }
}
