using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;
internal sealed class RibbonCohomologyRankDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact binary rank from literal boundary cycles of a one-vertex orientable ribbon.",
        H("Boundary cochains and binary interlacement"),
        Blocks(
            Describe.Lean(DescribeId.Create("literal-bouquet-interlacement-rank"),
                DeclarationHandle.Create(Owner+"literal_bouquet_boundary_interlace"),
                H("Literal boundary circles plus interlacement rank"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This is the one-circular-order form of the classical Cohn–Lempel equality (Journal of Combinatorial Theory A 13 (1972), 83–89, DOI 10.1016/0097-3165(72)90010-6). The inputs are an oriented cyclic dart order and an involution transposing precisely the selected disjoint pairs, while all unselected darts remain on the carrier as fixed points of the pairing.")),
                    Paragraph(Text("A field-valued function constant on boundary cycles is determined by its value at the initial dart and its oriented chord-endpoint differences. Each chord contributes two opposite increments; cyclic integration cancels them. Summing from the lower endpoint to the upper endpoint retains its own difference and the differences of exactly the interlacing chords. In characteristic two the orientation signs agree. The free initial value and the kernel of the actual interlacement map therefore count the boundary cycles.")),
                    Paragraph(Text("This is not a surface homology construction or a statement about arbitrary multi-vertex ribbon graphs; it is the literal one-vertex permutation count, with the boundary circles obtained without assuming an Euler formula."))),
                DescribeRole.Theorem))));
    private static Formula Statement()
    {
        var r = F.Id("R");
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create("R"),Call("ValidOrientedBouquetSwitches"),
            Equal(Call("Add",Call("BoundaryCircles",r),Call("BinaryInterlacementRank",r)),
                Call("Add",Num(1),Call("RetainedChords",r)))));
    }
}
