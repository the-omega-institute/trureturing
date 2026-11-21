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
            DescribeRole.Theorem))));
}
