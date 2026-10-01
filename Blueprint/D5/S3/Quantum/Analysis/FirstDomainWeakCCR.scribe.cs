using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class FirstDomainWeakCCRDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual position and momentum outputs satisfy the weak canonical relation on individual first L2 domains.",
        H("First-Domain Weak Canonical Relation"),
        Blocks(Describe.Lean(
            DescribeId.Create("first-domain-weak-ccr"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/FirstDomainWeakCCR.first_domain_weak_ccr"),
            H("Actual position and weak momentum"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("All MemLp conditions and integrals use real-line Lebesgue measure volume. "
                    + "The six witnesses hf, hg, hdf, hdg, hxf and hxg provide the L2 classes. "
                    + "[u] denotes the class of u, X(u) is x mapping to x times u(x), Q(u)=[X(u)], "
                    + "and P(v)=-i h [v]. The positive real scalar h is the Planck scalar hbar. Here a=df and b=dg. Complex inner products are "
                    + "conjugate-linear in the first variable and linear in the second.")),
                Paragraph(Text("T consists of every real-valued C-infinity compactly supported test function, "
                    + "with ContDiff Real (WithTop.some ENat.top) and HasCompactSupport. Its values and "
                    + "ordinary derivatives are cast into Complex in the displayed integrals. "
                    + "The two weak equations specify the actual maximal first derivative domains.")),
                Paragraph(Text("Actual modulation U(s)[u]=[exp(isx)u(x)] has strong L2 derivative iQ(u): "
                    + "its slopes are bounded by |xu| and its squared errors by 4|xu| squared. "
                    + "Dominated convergence proves this derivative. The translation-domain equivalence "
                    + "gives the actual derivatives for V(t)[u]=[u(x+t)]. Differentiating the bounded "
                    + "Weyl pairing identity twice, once in each real parameter, gives the displayed "
                    + "positive sign. Only individual first domains are used; the statement requires "
                    + "neither an operator-product domain nor second derivatives."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g"), a = F.Id("a"), b = F.Id("b"), h = F.Id("h");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula function = new Formula.TypeArrow(real, complex);
        Formula hypotheses = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, h);
        foreach (Formula u in new[] { f, g, a, b, Call("X", f), Call("X", g) })
            hypotheses = And(hypotheses, Call("MemLp", u, D(2), new Formula.NamedConstant(FormulaIdentifier.Create("volume"))));
        hypotheses = And(hypotheses, And(Weak(f, a), Weak(g, b)));
        Formula result = Equal(
            new Formula.Binary(Call("inner", Call("Q", f), Call("P", b)),
                FormulaBinaryOperator.Subtract, Call("inner", Call("P", a), Call("Q", g))),
            Mul(Mul(F.Id("i"), h), Call("inner", Bracket(f), Bracket(g))));
        return All([Bound("h", real), Bound("f", function), Bound("g", function),
            Bound("a", function), Bound("b", function)],
            new Formula.Logic(Parenthesized(hypotheses), FormulaLogicOperator.Implies, result));
    }
    private static Formula Weak(Formula u, Formula v)
    {
        Formula p = F.Id("p"), x = F.Id("x");
        return All([Bound("p", F.Id("T"))], Equal(
            Integral(Mul(Call("deriv", p, x), Apply(u, x))),
            Seq(Minus, Integral(Mul(Apply(p, x), Apply(v, x))))));
    }
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, Formula value) => new Formula.Apply(function, [value]);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Bracket(Formula f) => Seq(OpenBracket, f, CloseBracket);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Integral(Formula expression) => Seq(Int, Underscore, Grp(F.Id("x"), Colon, Sp,
        Mathbb, Grp(F.Id("R"))), Sp, expression, Sp, F.Id("dx"));
}
