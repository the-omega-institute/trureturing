using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class ParityProfileMatchingDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var w = F.Id("w");
        var i = F.Id("i");
        var count = Call("CommonOne", w, i);
        var best = Call("Best", n, k);
        var couplings = Call("Couplings", n, k);
        var coordinates = Call("Coordinates", n);
        var lower = Bind(FormulaQuantifier.Exists, "w", couplings,
            Bind(FormulaQuantifier.ForAll, "i", coordinates, Seq(best, Sp, Le, Sp, count)));
        var upper = Bind(FormulaQuantifier.ForAll, "w", couplings,
            Bind(FormulaQuantifier.Exists, "i", coordinates, Seq(count, Sp, Le, Sp, best)));
        return Disp(Bind(FormulaQuantifier.ForAll, "n", F.Id("Nat"),
            Bind(FormulaQuantifier.ForAll, "k", F.Id("Nat"),
                new Formula.Logic(Seq(D(0), Sp, Lt, Sp, k), FormulaLogicOperator.Implies,
                    Seq(Open, new Formula.Logic(Seq(Open, lower, Close), FormulaLogicOperator.And,
                        Seq(Open, upper, Close)), Close)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer couplings of the two parity classes have a sharp common-one count across coordinates.",
        H("Optimal common-one counts in parity couplings"),
        Blocks(Describe.Lean(
            DescribeId.Create("optimal-parity-coupling-common-count"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Hypercube/ParityProfileMatching.best_profile_count"),
            H("The greatest minimum common-one count"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Coordinates(n) is Fin(n+2). Couplings(n,k) consists of matrices " +
                    "of natural counts from the even profiles to the odd profiles with every row " +
                    "sum and every column sum equal to k. CommonOne(w,i) sums the entries whose " +
                    "two profiles both have bit one at i. With M = k times 2 to the power n, " +
                    "Best(n,k) is M minus the ceiling of M divided by n+2.")),
                Paragraph(Text("Each coordinate has M units of weight at bit one in each marginal. " +
                    "The total mismatch weight in that coordinate is twice the difference between " +
                    "M and its common-one count. Opposite parity forces at least one mismatch per " +
                    "weighted pair, so the sum of the differences across coordinates is at least M.")),
                Paragraph(Text("For attainment, distribute M units among the coordinates using the " +
                    "ceiling as a capacity and split the allocation into k batches of size 2 to the " +
                    "power n. Doubling the entries in each batch gives the even direction counts " +
                    "of a perfect matching by the Felzenbaum, Holzman and Kleitman criterion. " +
                    "The sum of the matching matrices realizes the bound."))),
            DescribeRole.Theorem))));
}
