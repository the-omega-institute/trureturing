using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityThreeOrbitTableDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var k = F.Id("k");
        var z = F.Id("z");
        var equivalence = new Formula.Logic(Call("Realizable", D(1), k, z),
            FormulaLogicOperator.Iff, Call("HasOrbitTable", k, z));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"),
            F.Id("Nat"), new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("z"),
                Call("CountVectors", D(3)), equivalence)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer orbit tables for uniform coloured parity in three coordinates.",
        H("Three-coordinate orbit tables"),
        Blocks(Describe.Lean(DescribeId.Create("exact-three-coordinate-orbit-table"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityThreeOrbitTable.exact_orbit_table"),
            H("Orbit table feasibility is equivalent to realization"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("CountVectors(3) consists of natural-valued functions on Fin(3). "
                    + "Realizable(1,k,z) requires an equivariant seed action on 16k seeds, uniform "
                    + "coloured even and odd parity marginals, and fixed counts z.")),
                Paragraph(Text("Order the even words as 000, 011, 101, 110 and the odd words as "
                    + "their complements. HasOrbitTable(k,z) requires a multiplicity and a fixed "
                    + "count for each orbit and coordinate. The all-ones odd column has two "
                    + "orbits of size two at each row, one for each right colour. Every other "
                    + "cell has one orbit of size four.")),
                Paragraph(Text("At each row the sum of the two special multiplicities plus "
                    + "twice the sum of the ordinary multiplicities is 2k. Each ordinary "
                    + "column and each special colour column have multiplicity sum k. Each "
                    + "fixed entry is at most its multiplicity and has the same parity. To "
                    + "obtain z at a coordinate, keep just the entries whose two words have "
                    + "bit one there and weight each entry by its orbit size.")),
                Paragraph(Text("An implementation gives the table by counting fibres. The "
                    + "converse uses the simultaneous orbit fibre criterion. Entries at "
                    + "coordinates moved by the output action do not enter the totals."))),
            DescribeRole.Theorem))));
}
