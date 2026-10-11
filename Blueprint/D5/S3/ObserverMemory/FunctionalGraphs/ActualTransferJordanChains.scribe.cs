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
                    + "complex numbers and put n=Nat.card(Y). The basis index is the dependent sum "
                    + "of Fin(val(s(i))) over the finite type I, with s(i) positive. The lengths form the "
                    + "multiset mapping s over Finset.univ.val, retaining multiplicities. The basis "
                    + "belongs to transientSubspace(tau,n), the generalized zero-eigenspace. "
                    + "The conditional basis vector is used only when its index is in range. "
                    + "Subtraction of natural numbers is truncated; Nat.pred is the natural predecessor.")),
                Paragraph(Text("The general nilpotent chain theorem supplies the actual basis "
                    + "and iterate ranks. Rank-nullity computes its kernel tower; the existing "
                    + "finite tower uniqueness theorem identifies its positive size multiset "
                    + "with transferZeroBlocks(tau). Thus the profile in the existing information "
                    + "loss theorem now has a basis of actual chains. All four source equality "
                    + "leaves are retained. totalInformationLoss is the finite-support sum of "
                    + "positive loss layers, as defined by the existing finite-map theory."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var symbol = Seq(Operatorname, Grp(name.Split('.').SelectMany((part, i) =>
            i == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray()));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name),
            type is Formula.TypeArrow ? Parenthesized(type) : type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Pair(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, Sp, y, Rangle);
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Power(Formula f, Formula m) => new Formula.Power(Parenthesized(f), m);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);

    private static Formula TheoremFormula()
    {
        var y = F.Id("Y"); var tau = F.Id("tau"); var index = F.Id("I"); var s = F.Id("s");
        var m = F.Id("m"); var i = F.Id("i"); var j = F.Id("j"); var k = F.Id("k");
        var n = Call("Nat.card", y);
        var size = Call("val", At(s, i));
        var next = Seq(Call("val", j), Sp, Plus, Sp, m);
        var positions = Parenthesized(Seq(Sigma, Sp,
            Parenthesized(Seq(i, Sp, Colon, Sp, index)), Comma, Sp, Call("Fin", size)));
        var nextIndex = Parenthesized(Seq(Call("Fin.mk", next), Sp, Colon, Sp, Call("Fin", size)));
        var blocks = Call("Multiset.map", s, Call("val", Parenthesized(Seq(
            Call("Finset.univ"), Sp, Colon, Sp, Call("Finset", index)))));
        var transient = Call("transientTransfer", tau, n);
        var action = All("m", Nats, All("i", index, All("j", Call("Fin", size),
            Eqn(At(Power(transient, m), At(F.Id("b"), Pair(i, j))),
                Call("ite", new Formula.Relation(next, FormulaRelationOperator.LessThan, size),
                    At(F.Id("b"), Pair(i, nextIndex)), D(0))))));
        Formula Rank(Formula exponent) => Call("Module.finrank", Complexes,
            Call("LinearMap.range", Power(Call("transferOperator", tau), exponent)));
        Formula Loss(Formula exponent) => Call("informationLossLayer", tau, exponent);
        var counts = All("k", Nats,
            Implies(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k),
                And(And(Eqn(Loss(k), Sub(Rank(Call("Nat.pred", k)), Rank(k))),
                        Eqn(Loss(k), Call("blockCountAtLeast", blocks, k))),
                    And(Eqn(Call("blockCountExactly", blocks, k),
                            Sub(Loss(k), Loss(Seq(k, Sp, Plus, Sp, D(1))))),
                        Eqn(Call("totalInformationLoss", tau),
                            Sub(n, Call("Nat.card", Call("PeriodicCore", tau))))))));
        var conclusion = Some("I", Call("Type"), Assumption(Call("Fintype", index),
            Some("s", new Formula.TypeArrow(index, Call("PNat")),
                Some("b", Call("Basis", positions, Complexes, Call("transientSubspace", tau, n)),
                    And(action, And(Eqn(blocks, Call("transferZeroBlocks", tau)), counts))))));
        return Disp(All("Y", Call("Type"), Assumption(Call("Finite", y),
            All("tau", new Formula.TypeArrow(y, y), conclusion))));
    }
}
