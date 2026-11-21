using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class GridReadoutConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/GridReadoutConstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivariant readout from scaled allocations on profile stabilizer blocks.",
        H("Calibrating probability grids by scaled block allocations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scaled-block-allocation-readout"),
                DeclarationHandle.Create(Prefix + "law_of_scaled_block_allocations"),
                H("A calibrating law from scaled common block allocations"),
                StatementSource.FromAuthor(ScaledAllocationStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be the number of labels, m the denominator, n the number of proposed "
                        + "regular seed orbits, and c a positive integer scale. The nonnegative "
                        + "integer orbit weights w have total c times m divided by k times (k minus one). "
                        + "ScaledBlockCover means the following. For every positive number of groups t, "
                        + "block count U at least k times (t minus one), and natural demands x whose sum "
                        + "times k times (k minus one) equals U times m, there is a common allocation. "
                        + "It assigns U blocks per orbit and gives each group weighted mass c times its demand.")),
                    Paragraph(Text(
                        "For each profile, split the labels into equal-coordinate groups. The group "
                        + "demands are integral because k minus one divides m. Use the allocations to "
                        + "construct a readout on its stabilizer blocks and transport the readout from "
                        + "one representative per profile orbit. Remove the zero-weight orbits and "
                        + "normalize the remaining mass to obtain a shared calibrating law."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula ScaledAllocationStatement()
    {
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula c = F.Id("c");
        Formula w = F.Id("w");
        Formula predecessor = Seq(Open, k, Minus, D(1), Close);
        return Disp(Seq(Forall, Sp, k, Sp, m, Sp, n, Sp, c, Sp, w, Comma, Sp,
            D(2), Sp, Le, Sp, k, Sp, Land, Sp, D(0), Sp, Lt, Sp, m, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, c, Sp, Land, Sp, Call("Divides", predecessor, m), Sp, Land, Sp,
            k, Cdot, predecessor, Cdot, Call("TotalWeight", w), Sp, Eq, Sp, c, Cdot, Sp, m,
            Sp, Land, Sp, Call("ScaledBlockCover", k, m, n, c, w), Sp, Rightarrow, Sp,
            Call("SeedBudget", k, m, Seq(Call("factorial", k), Cdot, Sp, n))));
    }
}
