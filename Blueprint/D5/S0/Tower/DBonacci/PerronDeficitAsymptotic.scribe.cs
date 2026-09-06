using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciPerronDeficitAsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var root = Call("dbonacciPerronRoot", d);
        var deficit = Subtract(Num(2), root);
        var binaryScale = Call("pow", Call("inv", Num(2)), d);
        var normalizedDeficit = Call("div", deficit, binaryScale);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The d-bonacci Perron-root deficit is sharply asymptotic to the negative d-th power of two.",
            H("D-Bonacci Perron Deficit Asymptotic"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("d-bonacci-perron-deficit-asymptotic"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronDeficitAsymptotic."
                            + "dbonacci_perron_deficit_asymptotic"),
                    H("The normalized Perron deficit tends to one"),
                    StatementSource.FromAuthor(Equal(
                        Call("limitAtTop", d, normalizedDeficit),
                        Num(1))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every order d at least two, the frozen characteristic-equation "
                                + "identity rewrites the endpoint deficit as the negative d-th "
                                + "power of the Perron root. Dividing by 2 to the negative d then "
                                + "gives the d-th power of 2 divided by that root.")),
                        Paragraph(Text(
                            "The logarithm of this normalized ratio is nonnegative. Its scaled "
                                + "value is bounded above by the golden-ratio reciprocal times d "
                                + "times the d-th power of that reciprocal. Mathlib's polynomial-"
                                + "times-geometric limit sends this majorant to zero, and continuity "
                                + "of the real exponential sends the normalized deficit to one.")),
                        Paragraph(Text(
                            "The denominator is nonzero for every natural order. The totalized "
                                + "values below order two do not affect the at-top limit, and no "
                                + "numerical approximation is used."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/PerronRoot")),
            ]));
    }
}
