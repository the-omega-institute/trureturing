using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedCountSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum";

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Group(Formula body) => Seq(Open, body, Close);

    private static Formula Divisibility()
    {
        var n = F.Id("n");
        var a = F.Id("A");
        var i = F.Id("i");
        var q = F.Id("q");
        var equation = Seq(Call("FixedCount", a, i), Sp, Eq, Sp, D(4), Sp, Cdot, Sp, q);
        return Disp(All("n", F.Id("Nat"), All("A", Call("UniformRealizations", n),
            All("i", Call("Coordinates", n), Exists("q", F.Id("Nat"), equation)))));
    }

    private static Formula ZeroVector()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var parity = Or(Call("Odd", Add(n, D(2))), Call("Even", k));
        return Disp(All("n", F.Id("Nat"), All("k", F.Id("Nat"),
            Iff(Call("Realizable", n, k, Call("ZeroVector", n)), Group(parity)))));
    }

    private static Formula TwoCoordinates()
    {
        var k = F.Id("k");
        var z = F.Id("z");
        var s = F.Id("s");
        var t = F.Id("t");
        var sum = Add(s, t);
        var counts = Call("PairVector", Seq(D(4), Sp, Cdot, Sp, s), Seq(D(4), Sp, Cdot, Sp, t));
        var magnitude = Seq(sum, Sp, Le, Sp, k);
        var parity = Or(Call("Even", k), Seq(D(0), Sp, Lt, Sp, sum));
        var constraints = And(Seq(z, Sp, Eq, Sp, counts), Group(And(magnitude, Group(parity))));
        return Disp(All("k", F.Id("Nat"), All("z", Call("CountVectors", D(0)),
            Iff(Call("Realizable", D(0), k, z),
                Group(Exists("s", F.Id("Nat"), Exists("t", F.Id("Nat"), constraints)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual fixed-seed counts of coloured parity couplings obey orbit divisibility.",
        H("Attainable fixed counts for coloured parity seeds"),
        Blocks(
            Describe.Lean(DescribeId.Create("parity-coordinate-fixed-count-fourfold"),
                DeclarationHandle.Create(Module + ".coordinate_fixed_count_four_dvd"),
                H("Fourfold divisibility of each coordinate fixed count"),
                StatementSource.FromAuthor(Divisibility()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Coordinates(n) is Fin(n+2). UniformRealizations(n) consists of finite seed " +
                        "sets with the coordinate colour action and an equivariant map into the even and odd " +
                        "coloured profile sets. Each possible output in either readout has the same seed count. " +
                        "FixedCount(A,i) counts seeds fixed by the subgroup acting in coordinate i.")),
                    Paragraph(Text("The seeds whose output pair is fixed by that subgroup have total count " +
                        "divisible by four. Separate out those moved by the generator. A two-point seed orbit " +
                        "mapping to a moving output orbit maps bijectively, so on this subset every orbit " +
                        "has size divisible by four. The difference is the actual fixed count."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity-seed-zero-vector"),
                DeclarationHandle.Create(Module + ".zero_coordinate_counts_iff"),
                H("When every coordinate has zero fixed count"),
                StatementSource.FromAuthor(ZeroVector()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Realizable(n,k,z) means that one uniform coloured parity realization " +
                        "with 2 to the power n+3 times k seeds gives count vector z. ZeroVector(n) is zero " +
                        "in every coordinate.")),
                    Paragraph(Text("Complement pairing works in odd dimension. In even dimension a fibre " +
                        "above one colour of the all-ones output has size 2k. If every fixed count vanishes, " +
                        "each orbit in this fibre has size divisible by four. Conversely, an even budget " +
                        "multiplier permits a binary label flipped by every coordinate generator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity-seed-two-coordinate-spectrum"),
                DeclarationHandle.Create(Module + ".exact_two_coordinate_counts"),
                H("Exact fixed-count vectors in dimension two"),
                StatementSource.FromAuthor(TwoCoordinates()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("CountVectors(n) consists of natural-valued functions on Coordinates(n). " +
                        "PairVector(a,b) gives the counts a and b in the first and second coordinates.")),
                    Paragraph(Text("Every vector is bounded by an attained boundary vector and each entry " +
                        "is divisible by four. A disjoint union adds both counts and budget multipliers. " +
                        "An implementation with sixteen seeds and counts (4,0), and its coordinate swap, " +
                        "provide the extra unit of multiplier when the unused multiplier is odd."))),
                DescribeRole.Theorem))));
}
