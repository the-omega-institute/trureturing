using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class DBonacciGeneralChampionBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var betaD = Call("beta", d);
        var limit = Equal(
            Call("limitAtTop", d, Call("championValue", betaD)),
            new Formula.Fraction(Num(1), Num(3)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The d-bonacci champion values converge to one third at the binary boundary.",
            H("D-Bonacci Champion Boundary"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("d-bonacci-champion-values-tend-to-one-third"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionBoundary."
                        + "championValue_dbonacciPerronRoot_tendsto_one_third"),
                    H("Champion values tend to one third"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(limit)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The Perron roots beta(d) tend to two. The denominator of the "
                                + "corrected rational champion expression is three at two, so "
                                + "the expression is continuous there and the composed sequence "
                                + "tends to championValue(2)=1/3.")),
                        Paragraph(Text(
                            "This is a filter-level limit as d tends to infinity. It is stronger "
                                + "than direct substitution at the endpoint."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
