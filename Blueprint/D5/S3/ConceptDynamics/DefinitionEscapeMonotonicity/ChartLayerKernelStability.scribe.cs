using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity;

internal sealed class ChartLayerKernelStabilityDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/"
            + "ChartLayerKernelStability.chart_layer_preserves_escape_dimension";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Image-injective chart postprocessing preserves kernel-derived escape data and dimension.",
        H("Chart Layer Kernel Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chart-layer-preserves-escape-dimension"),
                DeclarationHandle.Create(Gid),
                H("Image-injective chart layers preserve escape dimension"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the next chart readout be a postprocessing h of the current "
                            + "readout. The only injectivity required of h is on values "
                            + "actually realized by the current readout.")),
                    Paragraph(Text(
                        "The imported postprocessing kernel criterion gives equality of the "
                            + "two Setoid.ker relations. Any escape layer determined by that "
                            + "relation is therefore unchanged.")),
                    Paragraph(Text(
                        "The source atom does not define d_esc. The Lean declaration treats "
                            + "the escape layer and its ordered dimension as abstract readouts; "
                            + "equality of the layer makes the dimension equal, hence in "
                            + "particular nonincreasing."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula current = new Formula.Subscript(F.Id("q"), F.Id("k"));
        Formula next = new Formula.Subscript(F.Id("q"), Add(F.Id("k"), D(1)));
        Formula postprocess = F.Id("h");
        Formula currentKernel = Call("ker", current);
        Formula nextKernel = Call("ker", next);
        Formula currentEscape = Call("E", currentKernel);
        Formula nextEscape = Call("E", nextKernel);
        Formula escapeDimension = new Formula.Subscript(F.Id("d"), F.Id("esc"));
        Formula currentDimension = Seq(escapeDimension, Open, currentEscape, Close);
        Formula nextDimension = Seq(escapeDimension, Open, nextEscape, Close);

        return Disp(new Formula.Aligned([
            Seq(
                next, Sp, Eq, Sp, postprocess, Sp, Circ, Sp, current, Comma, Sp,
                Call("InjOn", postprocess, Call("range", current)), Sp,
                Rightarrow),
            Seq(
                nextKernel, Sp, Eq, Sp, currentKernel, Sp, Land, RowBreak,
                Grp(), nextEscape, Sp, Eq, Sp, currentEscape, Sp, Land),
            Seq(nextDimension, Sp, Leq, Sp, currentDimension, Dot),
        ]));
    }
}
