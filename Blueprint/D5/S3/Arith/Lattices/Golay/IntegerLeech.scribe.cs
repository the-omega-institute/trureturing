using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class IntegerLeechDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/IntegerLeech.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/leech1967packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integral Golay construction and its exact minimum",
        H("The integral Golay construction and its exact minimum"),
        Blocks(
            Node("representation", "representation", "The exact quotient representation",
                "The original admissibility conditions are equivalent to coordinates m plus twice an integer vector, with the same canonical parity bit, code residue and coordinate-sum congruence. The same integer representative determines both the real image and the raw coordinates in direct selfduality.", DescribeRole.Theorem),
            Node("claim-1", "Admissible", "Literal integral congruence coordinates",
                "An integer vector has a common parity bit m in zero or one; its quotient residue is a codeword, and its coordinate sum is congruent to four m modulo eight.", DescribeRole.Definition),
            Node("claim-2", "integerLattice", "Additive closure is derived",
                "For an arbitrary binary linear code containing the all-ones word, the literal congruence set is an additive subgroup. The odd plus odd carry is absorbed by the proved all-ones membership.", DescribeRole.Definition),
            Node("claim-3", "squareSum_div_sixteen", "Even scaled norms",
                "For every doubly-even binary linear code and every actual admissible integer vector, the sum of coordinate squares is divisible by sixteen. Dividing by eight therefore gives an even integral squared norm.", DescribeRole.Theorem),
            Node("claim-4", "construction_lower_bound", "Every nonzero admissible integer vector has squared integer norm at least 32",
                "The even nonzero-residue case uses the minimum weight. The zero-residue case uses the coordinate-sum congruence to exclude a sole coordinate of size four. In the odd case every coordinate has absolute value at least one and divisibility by sixteen raises the bound from 24 to 32.", DescribeRole.Theorem),
            Node("claim-5", "pairing_integral", "The scaled pairing is integral",
                "Polarization, the derived additive closure and divisibility of all three squared norms by sixteen imply divisibility of the coordinate dot product by eight.", DescribeRole.Theorem),
            Node("claim-6", "minimum_norm", "Exact minimum four from actual encoded Golay words",
                "This theorem consumes the constructed Golay linear image and its proved double evenness and minimum weight. Twice the zero-one lift of its encoded octad is an admissible nonzero vector with square sum 32. Every nonzero admissible vector has square sum at least 32, so dividing by eight gives exact squared minimum four. Coordinate division by the real square root of eight gives the same real squared norm as the rational square sum divided by eight. Rank, unimodularity, uniqueness and all VOA, CFT or Monster realization claims remain outside this result.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
