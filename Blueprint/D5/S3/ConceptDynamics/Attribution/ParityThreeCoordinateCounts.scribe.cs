using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityThreeCoordinateCountsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts";

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Leq(Formula left, Formula right) =>
        Seq(left, Sp, Le, Sp, right);

    private static Formula At(string name, Formula index) =>
        new Formula.Subscript(F.Id(name), index);

    private static Formula Statement()
    {
        var k = F.Id("k");
        var u = F.Id("u");
        var z = F.Id("z");
        var i = F.Id("i");
        var total = Call("Total", u);
        var coordinates = Call("Fin", D(3));
        var vectors = Call("CountVectors", D(3));
        var minusOne = Seq(Open, k, Sp, Minus, Sp, D(1), Close);
        var scale = All("i", coordinates, Seq(At("z", i), Sp, Eq, Sp, Mul(D(4), At("u", i))));
        var cap = All("i", coordinates, Leq(At("u", i), Mul(D(2), k)));
        var oddCut = All("i", coordinates, Leq(Mul(D(2), At("u", i)), Add(total, Mul(D(2), minusOne))));
        var conditions = And(scale, And(cap, And(Leq(total, Mul(D(4), k)),
            new Formula.Logic(Call("Odd", k), FormulaLogicOperator.Implies, oddCut))));
        return Disp(All("k", F.Id("Nat"), All("z", vectors,
            new Formula.Logic(Call("Realizable", D(1), k, z), FormulaLogicOperator.Iff,
                Bind(FormulaQuantifier.Exists, "u", vectors, conditions)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full integer fixed-count spectrum of three uniformly coloured parity coordinates.",
        H("Three-dimensional fixed-seed counts at every budget"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-coordinate-fixed-count-spectrum"),
            DeclarationHandle.Create(Module + ".exact_three_coordinate_counts"),
            H("The box, total bound, and odd-budget cuts characterize attainable vectors"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("CountVectors(3) is the type of natural-valued functions on Fin(3). "
                + "Total(u) sums the three entries. Odd(k) means k has remainder one modulo two, "
                + "and k minus one is truncated subtraction. Realizable(1,k,z) requires an "
                + "equivariant seed action with 16k seeds, uniform coloured even and odd "
                + "marginals, and actual coordinate fixed counts z.")),
                Paragraph(Text("The orbit fibre criterion supplies one multiplicity and one "
                + "fixed count at each relevant coordinate per output orbit. The ordinary "
                + "cells are four-point orbits. Each cell in the all-ones odd column contains "
                + "one two-point orbit per right colour. At odd k the parities of these "
                + "multiplicities obstruct the two possible saturations of a coordinate.")),
                Paragraph(Text("The minimum-budget criterion supplies the multiplier-one "
                + "block. Four pairs of matchings certify all multiplier-two vectors up to "
                + "coordinate permutation. Decompositions of integer vectors add these "
                + "blocks within the stated bounds and preserve both marginals."))),
            DescribeRole.Theorem))));
}
