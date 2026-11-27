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
            Call("RealizedFibresAndCounts", dimension, multiplier, weights, counts)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate fixation from coloured parity cell multiplicities.",
        H("Realize a coloured parity table by a common seed action"),
        Blocks(Describe.Lean(
            DescribeId.Create("invariant-parity-weights-with-fibres"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization.weighted_realization_with_fibres"),
            H("Invariant pair weights and joint fibre sizes"),
            StatementSource.FromAuthor(Disp(new Formula.Logic(
                Call("InvariantWeightsAndCounts", F.Id("d"), F.Id("k"), F.Id("w"), F.Id("z")),
                FormulaLogicOperator.Implies,
                Call("RealizedFibresAndCounts", F.Id("d"), F.Id("k"), F.Id("w"), F.Id("z"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let d be at least two and let k be a natural number. "
                + "Let w be a nonnegative integer weight on each output pair, invariant under "
                + "the common action, with both coloured marginals equal to 2k. At each "
                + "coordinate, let z be the sum of w modulo two over the output pairs whose "
                + "two profiles both contain that coordinate. One equivariant seed action "
                + "with k times 2 raised to the power (d + 1) seeds has those coloured "
                + "marginals, fixes z(i) seeds at each coordinate i, and has exactly w(a) "
                + "seeds over every output pair a."))),
            DescribeRole.Theorem),
            Describe.Lean(
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
                Paragraph(Text("A common equivariant seed action has k times 2 raised to the "
                    + "power (d + 1) seeds, with both coloured marginals equal to 2k at every point. "
                    + "At coordinate i its fixed count is twice the sum of each entry modulo two, "
                    + "summed over the cells whose two profiles both contain i and both left colours. "
                    + "For each pair of profiles and any two colours, the joint fibre size "
                    + "is exactly the entry indexed by the profiles and the left colour.")),
                Paragraph(Text("Coordinate shifts preserve each profile. The full even profile "
                    + "also preserves its colour. The multiplicity therefore descends to the "
                    + "output orbit. Within the fibre of any fixed output point the least allowed "
                    + "number of fixed seeds is its size modulo two. The orbit criterion realizes "
                    + "these least counts simultaneously."))),
            DescribeRole.Theorem))));
}
