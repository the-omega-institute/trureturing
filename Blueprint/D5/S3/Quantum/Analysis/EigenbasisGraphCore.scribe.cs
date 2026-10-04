using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class EigenbasisGraphCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted coefficients describe the genuine closure graph and its simultaneous finite core.",
        H("Eigenbasis Graph and Finite Core"),
        Blocks(Describe.Lean(
            DescribeId.Create("eigenbasis-actual-graph-coefficients-core"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/EigenbasisGraphCore.eigenbasis_graph_coefficients"),
            H("The actual finite operator determines the weighted graph"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be any complete complex inner product space, e a Hilbert basis "
                    + "with arbitrary index type I, and T a complex linear partial operator whose "
                    + "domain is exactly the algebraic span of e. Assume T sends e of i to lambda "
                    + "of i times e of i, with arbitrary real lambda. K is the genuine closure of T. "
                    + "Write c of i of x for the inner product of e of i with x.")),
                Paragraph(Text("For every x and y in H, the pair x and y belongs to the actual graph "
                    + "of K exactly when c of i of y equals lambda of i times c of i of x for every i. "
                    + "The domain of K consists exactly of vectors whose weighted coefficient family "
                    + "is square summable. The operator is not defined by that family.")),
                Paragraph(Text("Under the coefficient condition, let F range over finite subsets "
                    + "of I directed by inclusion. The vectors u of F are the finite sums of c of i "
                    + "of x times e of i over F. They lie in the actual domain of T. Their actual T "
                    + "images are the sums of lambda of i times c of i of x times e of i over the same F. "
                    + "The vectors converge to x and the images converge to y.")),
                Paragraph(Text("Hilbert expansion gives the two limits. Each finite pair is in "
                    + "the actual graph of T, so their product limit is in its graph closure. Symmetry "
                    + "of the self-adjoint closure gives the converse coefficient condition. Zero "
                    + "and repeated eigenvalues are allowed; no division by an energy is used."))),
            DescribeRole.Theorem))));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula TheoremFormula()
    {
        Formula h = F.Id("H"), i = F.Id("I"), e = F.Id("e"), t = F.Id("T"), l = F.Id("lambda");
        Formula x = F.Id("x"), y = F.Id("y"), j = F.Id("j"), f = F.Id("F"), u = F.Id("u");
        Formula k = Call("closure", t), finite = Call("Finset", i);
        Formula ei = new Formula.Apply(e, [j]), li = new Formula.Apply(l, [j]);
        Formula cx = Call("inner", ei, x), cy = Call("inner", ei, y), weight = Mul(li, cx);
        Formula coeff = All("j", i, Equal(cy, weight));
        Formula uf = new Formula.Apply(u, [f]), tuf = new Formula.Apply(t, [uf]);
        Formula sum = Call("sum", new Formula.Sequence(Mul(cx, ei), j, f));
        Formula wsum = Call("sum", new Formula.Sequence(Mul(weight, ei), j, f));
        Formula core = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("u"), new Formula.TypeArrow(finite, Call("domain", t)))],
            And(All("F", finite, Equal(uf, sum)), And(All("F", finite, Equal(tuf, wsum)),
                And(Call("Tendsto", new Formula.Sequence(uf, f, finite), x),
                    Call("Tendsto", new Formula.Sequence(tuf, f, finite), y)))));
        Formula conclusion = And(new Formula.Logic(Call("GraphMember", k, x, y),
            FormulaLogicOperator.Iff, coeff), And(new Formula.Logic(coeff, FormulaLogicOperator.Implies, core),
                new Formula.Logic(Call("DomainMember", k, x), FormulaLogicOperator.Iff,
                    Call("MemL2", new Formula.Sequence(weight, j, i)))));
        Formula assumptions = And(Equal(Call("domain", t), Call("span", Call("range", e))),
            All("j", i, Equal(new Formula.Apply(t, [ei]), Mul(li, ei))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexInnerProductSpace")),
             new(FormulaIdentifier.Create("I"), F.Id("Type")),
             new(FormulaIdentifier.Create("e"), Call("HilbertBasis", i, h)),
             new(FormulaIdentifier.Create("T"), Call("LinearPartialOperator", h)),
             new(FormulaIdentifier.Create("lambda"), new Formula.TypeArrow(i, Seq(Mathbb, Grp(F.Id("R"))))),
             new(FormulaIdentifier.Create("x"), h), new(FormulaIdentifier.Create("y"), h)],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
    }
}
