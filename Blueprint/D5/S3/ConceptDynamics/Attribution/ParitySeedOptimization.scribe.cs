using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedOptimizationDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var a = F.Id("A");
        var i = F.Id("i");
        var best = Call("BestCount", n, k);
        var fixedCount = Call("FixedCount", a, i);
        var coordinates = Call("Coordinates", n);
        var realizations = Call("UniformRealizations", n, k);
        var attained = Bind(FormulaQuantifier.Exists, "A", realizations,
            Bind(FormulaQuantifier.ForAll, "i", coordinates, Seq(best, Sp, Le, Sp, fixedCount)));
        var upper = Bind(FormulaQuantifier.ForAll, "A", realizations,
            Bind(FormulaQuantifier.Exists, "i", coordinates, Seq(fixedCount, Sp, Le, Sp, best)));
        return Disp(Bind(FormulaQuantifier.ForAll, "n", F.Id("Nat"),
            Bind(FormulaQuantifier.ForAll, "k", F.Id("Nat"),
                new Formula.Logic(Seq(D(0), Sp, Lt, Sp, k), FormulaLogicOperator.Implies,
                    Seq(Open, new Formula.Logic(Seq(Open, attained, Close), FormulaLogicOperator.And,
                        Seq(Open, upper, Close)), Close)))));
    }

    private static Formula MaximalVectors()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var v = F.Id("v");
        var u = F.Id("u");
        var z = F.Id("z");
        var i = F.Id("i");
        var countVectors = Call("CountVectors", n);
        var coordinates = Call("Coordinates", n);
        var dominates = Bind(FormulaQuantifier.ForAll, "i", coordinates,
            Seq(Call("Value", z, i), Sp, Le, Sp, Call("Value", u, i)));
        var maximal = Bind(FormulaQuantifier.ForAll, "u", countVectors,
            new Formula.Logic(Seq(Open, new Formula.Logic(Call("Realizable", n, k, u),
                FormulaLogicOperator.And, Seq(Open, dominates, Close)), Close),
                FormulaLogicOperator.Implies, Seq(u, Sp, Eq, Sp, z)));
        var exact = Bind(FormulaQuantifier.ForAll, "i", coordinates,
            Seq(Call("Value", z, i), Sp, Eq, Sp, D(4), Cdot, Call("Value", v, i)));
        var boundary = Bind(FormulaQuantifier.Exists, "v", countVectors,
            new Formula.Logic(Call("Boundary", n, k, v), FormulaLogicOperator.And,
                Seq(Open, exact, Close)));
        return Disp(Bind(FormulaQuantifier.ForAll, "n", F.Id("Nat"),
            Bind(FormulaQuantifier.ForAll, "k", F.Id("Nat"),
                Bind(FormulaQuantifier.ForAll, "z", countVectors,
                    new Formula.Logic(Seq(Open, new Formula.Logic(Call("Realizable", n, k, z),
                        FormulaLogicOperator.And, Seq(Open, maximal, Close)), Close),
                        FormulaLogicOperator.Iff, Seq(Open, boundary, Close))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum coordinate fixed mass has an exact optimum at each feasible positive seed budget.",
        H("Optimal fixed counts for coloured parity seeds"),
        Blocks(Describe.Lean(
            DescribeId.Create("optimal-coloured-parity-fixed-seed-count"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization.best_fixed_seed_count"),
            H("The greatest minimum coordinate fixed count"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Coordinates(n) is Fin(n+2). UniformRealizations(n,k) consists " +
                    "of finite group sets of size N = 2 to the power n+3 times k with an " +
                    "equivariant map to the product of the even and odd coloured parity classes. " +
                    "An acting binary vector adds its entries over the zero coordinates of an output " +
                    "profile to that output colour, leaving the profile fixed. " +
                    "The two readouts have the same seed count above each of their possible " +
                    "coloured outputs. FixedCount(A,i) counts seeds fixed by the subgroup that " +
                    "acts only in coordinate i. BestCount(n,k) is four times M minus four times " +
                    "the ceiling of M divided by n+2, where M is k times 2 to the power n.")),
                Paragraph(Text("An equivariant map takes fixed seeds to fixed output pairs. " +
                    "Pooling the two colours and dividing each count by four gives an integer " +
                    "profile coupling of marginal multiplicity k. The sharp common-one bound " +
                    "for that coupling, multiplied by four, bounds the fixed-seed count.")),
                Paragraph(Text("Starting with a profile coupling that attains the sharp bound, " +
                    "retain every colour pair over each profile copy and let the group preserve " +
                    "the copy index. Then a seed is fixed in a coordinate exactly when both " +
                    "profile bits equal one in that coordinate."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pareto-boundary-of-coloured-parity-fixed-counts"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Attribution/ParitySeedOptimization.maximal_coordinate_fixed_vectors"),
                H("Maximal coordinate fixed-seed vectors"),
                StatementSource.FromAuthor(MaximalVectors()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("CountVectors(n) consists of natural-valued functions on " +
                        "Coordinates(n). Value(z,i) is the value of z at i. Realizable(n,k,z) " +
                        "means that one action and readout in UniformRealizations(n,k) has " +
                        "exactly z(i) seeds fixed at each coordinate i.")),
                    Paragraph(Text("Boundary(n,k,v) means that all entries of v are at most " +
                        "M = k times 2 to the power n, and the sum of M minus the entries " +
                        "of v equals M. Dividing pooled counts by four gives a profile coupling " +
                        "whose common-one counts bound the fixed-seed counts after scaling.")),
                    Paragraph(Text("The matching construction gives a profile boundary vector " +
                        "dominating the normalized counts. The colour-copy lift attains its " +
                        "scaled fixed counts simultaneously. All boundary vectors have the " +
                        "same coordinate sum."))),
                DescribeRole.Theorem))));
}
