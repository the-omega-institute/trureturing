using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntryMixtureBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict MTP2 for the actual finite single-entry forward law.",
        H("The positive mixture is derived from the generator"),
        Blocks(Describe.Lean(DescribeId.Create("single-entry-finite-network-strict-mtp"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/SingleEntryMixtureBridge.finite_network_strict_mtp2"),
            H("Every incomparable configuration pair has a strict minor"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The sites, binding and unbinding rates, inhibited state, initial unit mass in that state, and forward generator are the same as in SingleEntryFiniteNetwork. No positivity of a mixture or of a lattice minor is assumed. Transform the actual trajectory with the invertible free product basis. Each subset mode solves a scalar forced decay equation, with its free subset rate and its empty-configuration spectral weight. An integrating factor gives its convolution with the actual net return theta p(R)-eta p(empty). Reconstructing through the inverse basis and the finite subset-product expansion gives exactly the shared mixture of Bernoulli kernels g(i,u)=q(i)(1-exp(-s(i)u)). The actual net return is strictly positive at every nonnegative time, including the initial value theta. Each g is strictly increasing and lies in [0,1) on the integration interval. The ordered product-mixture theorem therefore gives a strict minor for every incomparable pair. The auxiliary variable is the free-kernel convolution variable; it is not identified with the last departure age from the inhibited state. The two selected actual sites and the inhibited conformation give the stated five-mode source after marginalizing the remaining sites. No finite Fibonacci native reader or continuation law is inferred from this source correspondence."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Statement()
    {
        Formula sites = F.Id("I"), k = F.Id("k"), p = F.Id("p"), t = F.Id("t");
        Formula s = F.Id("S"), r = F.Id("T");
        Formula state = Call("Option", Call("Finset", sites));
        Formula left = new Formula.Binary(Call("p", t, Call("some", s)),
            FormulaBinaryOperator.Multiply, Call("p", t, Call("some", r)));
        Formula right = new Formula.Binary(Call("p", t, Call("some", Call("inter", s, r))),
            FormulaBinaryOperator.Multiply, Call("p", t, Call("some", Call("union", s, r))));
        Formula notSubset = And(Seq(Neg, Sp, Call("Subset", s, r)), Seq(Neg, Sp, Call("Subset", r, s)));
        Formula body = All("k", Call("Rates", sites),
            All("p", Seq(R(), Sp, To, Sp, state, Sp, To, Sp, R()),
            Imp(Call("ForwardSolution", k, p), All("t", R(),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, t),
            All("S", Call("Finset", sites), All("T", Call("Finset", sites),
                Imp(notSubset, Rel(left, FormulaRelationOperator.LessThan, right)))))))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", sites), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", sites), CloseBracket, Sp, body)));
    }
}
