using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FunctionalGraphs;

internal sealed class InformationLossJordanLayersDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/FunctionalGraphs/InformationLossJordanLayers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observable loss layers are the rank drops and zero-block layers of a finite self-map.",
        H("Information-Loss Layers and Zero Jordan Chains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("information-loss-layers-and-zero-jordan-chains"),
                DeclarationHandle.Create(
                    Prefix + "information_loss_layers_and_zero_jordan_chains"),
                H("Information loss recovers every zero-block layer and its total"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau be a self-map of a finite carrier Y and let k be positive. "
                            + "The zeroBlocks parameter is tied to tau by the complete residual-"
                            + "rank equation already used by the repository's theorem 8.3 "
                            + "formalization; no unconditional Jordan classifier is claimed.")),
                    Paragraph(Text(
                        "The k-th observable loss equals the drop between the preceding and "
                            + "current transfer ranks and also counts zero blocks of size at "
                            + "least k. Blocks of exact size k are the difference of consecutive "
                            + "loss layers.")),
                    Paragraph(Text(
                        "The finite carrier stabilizes by card(Y), so totalInformationLoss is "
                            + "the finite support realization of the source's sum over all "
                            + "positive layers. It equals card(Y) minus the periodic-core card.")),
                    Paragraph(Text(
                        "The proof reuses the canonical observable filtration, transfer "
                            + "linearization, periodic core, stable-image theorem, and zero-block "
                            + "profile. Mathlib's Nat-valued telescoping theorem supplies the "
                            + "only new summation step."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), naturals = Call("Nat");
        Formula carrier = F.Id("Y"), update = F.Id("tau");
        Formula blocks = F.Id("zeroBlocks"), j = F.Id("j"), k = F.Id("k");
        Formula one = D(1);

        Formula power(Formula exponent) =>
            Call("pow", Call("transferOperator", update), exponent);
        Formula rank(Formula exponent) =>
            Call("finrank", Call("Complex"), Call("range", power(exponent)));
        Formula residualRank(Formula exponent) =>
            Call("natSub", rank(exponent), Call("card", Call("PeriodicCore", update)));
        Formula loss(Formula index) => Call("informationLossLayer", update, index);

        Formula rankProfile = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", naturals)],
            Equal(
                residualRank(j),
                Call("natSub", Call("blockProfileDimension", blocks),
                    Call("blockKernelTower", blocks, j))));
        Formula rankDrop = Call("natSub", rank(Call("pred", k)), rank(k));
        Formula firstClause = And(
            Equal(loss(k), rankDrop),
            Equal(loss(k), Call("blockCountAtLeast", blocks, k)));
        Formula exactClause = Equal(
            Call("blockCountExactly", blocks, k),
            Call("natSub", loss(k), loss(Call("add", k, one))));
        Formula totalClause = Equal(
            Call("totalInformationLoss", update),
            Call("natSub", Call("card", carrier),
                Call("card", Call("PeriodicCore", update))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Y", type),
                Bound("tau", Call("Function", carrier, carrier)),
                Bound("zeroBlocks", Call("BlockMultiset")),
                Bound("k", naturals),
            ],
            Implies(
                All(Call("Finite", carrier), rankProfile, Less(D(0), k)),
                All(firstClause, exactClause, totalClause))));
    }
}
