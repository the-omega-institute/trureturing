using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class ComplementSelectorDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise avoidance supplies the twist required for diagonal escape.",
        H("Complement Selector Diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("avoidance-selection-produces-diagonal-escape"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Negation/ComplementSelectorDiagonal."
                        + "avoidanceSelector_diagonal_escape"),
                H("Avoidance selection produces diagonal escape"),
                StatementSource.FromAuthor(EscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The catalog assigns an output to every address pair. Self-evaluation "
                            + "reads the diagonal value at an address, and the selector replaces "
                            + "that value by a distinct output.")),
                    Paragraph(Text(
                        "The selector's avoidance field supplies fixed-point-freedom for its "
                            + "choice function. The repository's qualitative Lawvere theorem then "
                            + "turns that pointwise inequality into escape from every catalog "
                            + "diagonal entry.")),
                    Paragraph(Text(
                        "No surjectivity, enumeration, or finiteness premise is used; the claim "
                            + "depends only on the explicitly typed catalog and the supplied "
                            + "avoidance-selector structure."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula EscapeFormula()
    {
        Formula address = F.Id("Address");
        Formula output = F.Id("Output");
        Formula selector = F.Id("selector");
        Formula catalog = F.Id("catalog");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, selector, Colon, Sp,
            Call("AvoidanceSelector", output), Comma, RowBreak, Grp(),
            catalog, Colon, Sp,
            Arrow(address, Arrow(address, output)), Comma, RowBreak, Grp(),
            Call("IsEscaped", Call("choose", selector), catalog), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
