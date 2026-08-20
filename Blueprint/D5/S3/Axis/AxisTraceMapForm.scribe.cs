using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisTraceMapFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var w1 = Id("w1");
        var w0 = Id("w0");
        var t1 = Id("t1");
        var t0 = Id("t0");

        var mapForm = Equal(
            Call("F", w1, w0, t1, t0),
            Call("tuple",
                Add(w1, Multiply(Multiply(t1, t0), w0)),
                w1,
                Multiply(t1, t0),
                t1));

        var step = Equal(
            Call("F", Call("state", Id("K"))),
            Call("state", Add(Id("K"), Num(1))));

        var iterate = Equal(
            Call("state", Id("K")),
            Call("iterate", Call("F", Id("K")), Call("state", Num(0))));

        const string declarationPrefix = "D5/S3/Axis/AxisTraceMapForm.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The four dimensional trace map has the stated form and carries the axis orbit.",
            H("Axis Trace Map Form"),
            Blocks(
                Paragraph(Text(
                    "The two axis recurrences can be read as a single map on four coordinates: "
                        + "the last two partial sums together with the last two weights. One "
                        + "step of that map produces the next sum, shifts the previous one, "
                        + "multiplies the two weights, and shifts the previous weight.")),
                Paragraph(Text(
                    "The orbit statement was already available, but it holds of whatever the "
                        + "map happens to be defined as. Pinning the four coordinates makes the "
                        + "definition checkable against the source line, which is why the form "
                        + "is a conjunct here rather than a comment.")),
                Paragraph(Text(
                    "The source also records that the orbit converges doubly exponentially, "
                        + "backed there by a numerical certificate rather than an argument. "
                        + "That half is not claimed.")),
                Describe.Lean(
                    DescribeId.Create("the-map-has-the-stated-four-coordinates"),
                    DeclarationHandle.Create(declarationPrefix + "orbitMap_form"),
                    H("The map has the stated four coordinates"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(mapForm)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Coordinate by coordinate against the source line. Changing any one of "
                            + "them makes the module fail to build, so the statement is bound "
                            + "to the definition rather than describing it."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-trace-map-clause-packaged"),
                    DeclarationHandle.Create(
                        declarationPrefix + "axis_trace_map_form_package"),
                    H("The trace map clause packaged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        new Formula.Logic(
                            mapForm,
                            FormulaLogicOperator.And,
                            new Formula.Logic(step, FormulaLogicOperator.And, iterate)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "One conjunction: the map has the stated coordinates, it carries the "
                            + "axis state one depth forward, and every state is an iterate of "
                            + "the initial one. Convergence is not among the conjuncts."))),
                    DescribeRole.Theorem))));
    }
}
