using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityColouredTableRealizationDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var dimension = F.Id("d");
        var multiplier = F.Id("k");
        var weights = F.Id("m");
        var counts = Call("LeastFibreCounts", dimension, weights);
        return Disp(new Formula.Logic(
            Call("ColouredMargins", dimension, multiplier, weights), FormulaLogicOperator.Implies,
            Call("RealizableCounts", dimension, multiplier, counts)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate fixation from coloured parity cell multiplicities.",
        H("Realize a coloured parity table by a common seed action"),
        Blocks(Describe.Lean(
            DescribeId.Create("coloured-parity-table-realization"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.realize_coloured_table"),
            H("Least fixed counts from coloured cell multiplicities"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The dimension d is at least two. The table m has a natural-number "
                    + "multiplicity for every even profile, odd profile, and binary left colour. "
                    + "Both right colours use that same multiplicity. Every even profile and left "
                    + "colour has marginal k. Every odd profile has marginal 2k after summing "
                    + "over even profiles and both left colours. The two left-colour entries "
                    + "coincide for every profile other than the full even profile.")),
                Paragraph(Text("A common equivariant seed action has 2 to the power d plus one, "
                    + "times k seeds, with both coloured marginals equal to 2k at every point. "
                    + "At coordinate i its fixed count is twice the sum of each entry modulo two, "
                    + "summed over the cells whose two profiles both contain i and both left colours.")),
                Paragraph(Text("Coordinate shifts preserve each profile. The full even profile "
                    + "also preserves its colour. The multiplicity therefore descends to the "
                    + "output orbit. Within the fibre of any fixed output point the least allowed "
                    + "number of fixed seeds is its size modulo two. The orbit criterion realizes "
                    + "these least counts simultaneously."))),
            DescribeRole.Theorem))));
}
