using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntrySlowTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic transfer of an independently supplied input asymptotic to the association residual.",
        H("Exact slow association coefficient"),
        Blocks(Describe.Lean(DescribeId.Create("single-entry-conditional-slow-tail"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/SingleEntrySlowTail.association_tail_from_input_tail"),
            H("The forced association tail"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Let D be the unnormalized association residual, f the actual net input and K the joint occupancy of the same chain. In the formula, weighted(l,f) denotes the function t mapped to exp(l t)f(t), apply(f,t) denotes f(t), h denotes theta and z denotes slope. Assume D'=-sD+fK, an input tail exp(l t)f(t) tending to -theta/slope, and a joint equilibrium K(t) tending to r q v. For l<s, positive theta,r,q,v and negative slope, the weighted residual exp(l t)D(t) tends to -theta r q v/((s-l)slope), and this coefficient is strictly positive. The input residue and the equilibrium are separate premises, not consequences of this theorem. In the proposed network application, l is to be identified with the secular root, slope with F'(l), r with the active equilibrium mass, and q,v with the free occupancies. Those identifications require independent generator and spectral evidence.")),
                Paragraph(Text(
                "The proof rescales y(t)=exp(l t)D(t), giving y'=-(s-l)y+g with g(t)=exp(l t)f(t)K(t). For a stable equation y'=-cy+g and g tending to L, each eventual forcing bound g<=cB gives the upper comparison y(t)<=B+exp(-c(t-T))(y(T)-B); the reversed bound gives the lower comparison. Both comparisons follow by differentiating exp(ct)(y(t)-B) and using its derivative sign. Choosing B on either side of L/c and letting time tend to infinity proves y tends to L/c. No asymptotic of D is assumed."))), DescribeRole.Theorem))));

    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
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
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Negate(Formula a) => Sub(D(0), a);
    private static Formula Pos(Formula a) => Rel(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Statement()
    {
        Formula d = F.Id("D"), f = F.Id("f"), k = F.Id("K"), s = F.Id("s"), l = F.Id("l");
        Formula h = F.Id("h"), r = F.Id("r"), q = F.Id("q"), v = F.Id("v"), z = F.Id("z"), t = F.Id("t");
        Formula forceLimit = Call("Tendsto", Call("weighted", l, f), Call("atTop"), Call("nhds", Div(Negate(h), z)));
        Formula jointLimit = Call("Tendsto", k, Call("atTop"), Call("nhds", Mul(Mul(r, q), v)));
        Formula ode = All("t", R(), Imp(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, t),
            Call("HasDerivAt", d, Seq(Negate(Mul(s, Call("apply", d, t))), Sp, Plus, Sp,
                Mul(Call("apply", f, t), Call("apply", k, t))), t)));
        Formula coefficient = Div(Mul(Mul(Mul(Negate(h), r), q), v), Mul(Sub(s, l), z));
        Formula conclusion = And(Call("Tendsto", Call("weighted", l, d), Call("atTop"), Call("nhds", coefficient)), Pos(coefficient));
        Formula premises = And(Rel(l, FormulaRelationOperator.LessThan, s), And(Pos(h), And(Pos(r),
            And(Pos(q), And(Pos(v), And(Rel(z, FormulaRelationOperator.LessThan, D(0)), And(ode, And(forceLimit, jointLimit))))))));
        Formula result = Imp(premises, conclusion);
        foreach (var name in new[] { "z", "v", "q", "r", "h", "l", "s" }) result = All(name, R(), result);
        Formula fn = Seq(R(), Sp, To, Sp, R());
        result = All("D", fn, All("f", fn, All("K", fn, result)));
        return Disp(result);
    }
}
