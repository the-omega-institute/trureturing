using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FunctionalGraphs;

internal sealed class ActualTransferJordanChainsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The transfer loss layers count actual Jordan chains on its transient Fitting summand.",
        H("Actual Transfer Jordan Chains"),
        Blocks(Describe.Lean(
            DescribeId.Create("information-loss-layers-from-actual-jordan-chains"),
            DeclarationHandle.Create("D5/S3/ObserverMemory/FunctionalGraphs/ActualTransferJordanChains."
                + "information_loss_layers_from_actual_jordan_chains"),
            H("Actual chains realize the rank-loss profile"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite Y and arbitrary self-map tau, work over the "
                    + "complex numbers and put n=card(Y). Positions(I,s) is the dependent sum "
                    + "of Fin(s(i)) over the finite type I, with s(i) positive. Sizes(I,s) is the "
                    + "multiset mapping s over all of I, retaining multiplicities. The basis "
                    + "belongs to transientSubspace(tau,n), the generalized zero-eigenspace. "
                    + "The conditional basis vector is used only when its index is in range. "
                    + "natSub means truncated natural subtraction and pred is the natural predecessor.")),
                Paragraph(Text("The general nilpotent chain theorem supplies the actual basis "
                    + "and iterate ranks. Rank-nullity computes its kernel tower; the existing "
                    + "finite tower uniqueness theorem identifies its positive size multiset "
                    + "with transferZeroBlocks(tau). Thus the profile in the existing information "
                    + "loss theorem now has a basis of actual chains. All four source equality "
                    + "leaves are retained. totalInformationLoss is the finite-support sum of "
                    + "positive loss layers, as defined by the existing finite-map theory."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula TheoremFormula()
    {
        Formula y = F.Id("Y"), tau = F.Id("tau"), index = F.Id("I"), s = F.Id("s");
        Formula m = F.Id("m"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula n = Call("card", y), size = Call("s", i), next = Call("add", j, m);
        Formula blocks = Call("Sizes", index, s), complex = Call("Complex");
        Formula transient = Call("transientTransfer", tau, n);
        Formula action = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("m", Call("Nat")), Bound("i", index), Bound("j", Call("Fin", size))],
            Eqn(Call("apply", Call("pow", transient, m), Call("b", i, j)),
                Call("ite", new Formula.Relation(next, FormulaRelationOperator.LessThan, size),
                    Call("b", i, next), D(0))));
        Formula rank(Formula exponent) =>
            Call("finrank", complex, Call("range", Call("pow", Call("transferOperator", tau), exponent)));
        Formula loss(Formula exponent) => Call("informationLossLayer", tau, exponent);
        Formula counts = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("k", Call("Nat"))],
            new Formula.Logic(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k),
                FormulaLogicOperator.Implies,
                All(All(Eqn(loss(k), Call("natSub", rank(Call("pred", k)), rank(k))),
                        Eqn(loss(k), Call("blockCountAtLeast", blocks, k))),
                    Eqn(Call("blockCountExactly", blocks, k),
                        Call("natSub", loss(k), loss(Call("add", k, D(1))))),
                    Eqn(Call("totalInformationLoss", tau),
                        Call("natSub", n, Call("card", Call("PeriodicCore", tau)))))));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("I", F.Id("Type")), Bound("hI", Call("Fintype", index)),
             Bound("s", Call("Function", index, Call("PNat"))),
             Bound("b", Call("Basis", Call("Positions", index, s), complex,
                Call("transientSubspace", tau, n)))],
            All(action,
                Eqn(blocks, Call("transferZeroBlocks", tau)), counts));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("Y", F.Id("Type")), Bound("tau", Call("Function", y, y))],
            new Formula.Logic(Call("Finite", y), FormulaLogicOperator.Implies, conclusion)));
    }
}
