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
                            + "The multiset transferZeroBlocks(tau) is constructed from consecutive "
                            + "rank-loss layers, rather than supplied as a parameter.")),
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
                        "Theorem 8.3 is proved internally: the conjugate-partition construction "
                            + "has the same complete power-kernel tower as the canonical transfer "
                            + "operator. At the finite stabilization exponent, the Fitting "
                            + "transient subspace is that kernel, its restricted transfer is "
                            + "nilpotent, and every restricted power kernel is linearly equivalent "
                            + "to the corresponding ambient kernel. This binds the constructed "
                            + "multiset to the actual generalized zero-eigenspace. Mathlib's "
                            + "Nat-valued telescoping theorem supplies the total-loss summation step."))),
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
        Formula k = F.Id("k");
        Formula blocks = Call("transferZeroBlocks", update);
        Formula one = D(1);

        Formula power(Formula exponent) =>
            Call("pow", Call("transferOperator", update), exponent);
        Formula rank(Formula exponent) =>
            Call("finrank", Call("Complex"), Call("range", power(exponent)));
        Formula loss(Formula index) => Call("informationLossLayer", update, index);

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
                Bound("k", naturals),
            ],
            Implies(
                All(Call("Finite", carrier), Less(D(0), k)),
                All(firstClause, exactClause, totalClause))));
    }
}
