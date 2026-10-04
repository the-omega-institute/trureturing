using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FiveOutcomeDyadicSupportBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FiveOutcomeDyadicSupportBound.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Indices => Call("Fin", D(5));
    private static Formula Laws => Seq(Indices, Sp, To, Sp, Real);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Power(Formula d) => new Formula.Superscript(D(2), d);
    private static Formula Term(Formula p, Formula d) =>
        new Formula.Fraction(Call("R", p, d), Power(d));
    private static Formula IndexedSum(Formula i, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, domain)), body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two supporting lines for the classical dyadic cost of every five-outcome real law.",
        H("Five-Outcome Dyadic Cost Support Bounds"),
        Blocks(
            Describe.Lean(DescribeId.Create("residual"), DeclarationHandle.Create(Prefix + "residual"),
                H("Dyadic residual"), StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromLiterature("lumbroso2013ddg"),
                Blocks(Paragraph(Text("R(p,d) counts unassigned dyadic cylinders algebraically. "
                    + "The floor is the integer floor. For a nonnegative real probability vector "
                    + "with five coordinates summing to one, R(p,d) is an integer between zero "
                    + "and four. Zero coordinates and terminating dyadic expansions are included."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cost"), DeclarationHandle.Create(Prefix + "cost"),
                H("Classical dyadic tail cost"), StatementSource.FromAuthor(CostFormula()),
                AssessedProvenance.FromLiterature("lumbroso2013ddg"),
                Blocks(Paragraph(Text("L(p) is the real infinite sum of these normalized residuals. "
                    + "The geometric bound four divided by 2 to the power d gives summability "
                    + "on the entire five-outcome simplex. The series expression is the classical "
                    + "Knuth-Yao DDG cost recalled by Lumbroso, Section 2.1. The support theorem "
                    + "below concerns this numerical series."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("support-bounds"), DeclarationHandle.Create(Prefix + "result"),
                H("Two affine supporting inequalities"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real probability vector on Fin(5), let t be its "
                    + "smallest coordinate. The series is summable, 0 <= t <= 1/5, and both "
                    + "16t <= L(p) and 48t-6 <= L(p) hold. No rationality or strict positivity "
                    + "hypothesis is imposed. For positive t, in the five consecutive intervals ending at "
                    + "1/16, 1/8, 5/32, 1/6 and 3/16, finite dyadic bucket budgets give "
                    + "partial-cost bounds 1, 2, 5/2, 11/4 and 3. Above 3/16 the vector "
                    + "q(i)=16p(i)-3 is again a probability vector and "
                    + "L(p)=27/8+L(q)/16. Iterating an error bound of size 4/16^n and taking "
                    + "its zero limit proves the second supporting line, including the uniform "
                    + "law. The two bounds supply necessary inequalities and assert no "
                    + "attainment claim for each prescribed smallest coordinate."))), DescribeRole.Theorem))));

    private static Formula ResidualFormula()
    {
        var p = V("p"); var i = V("i"); var d = V("d");
        return Disp(All(p, Laws, All(d, Nat, Equal(Call("R", p, d),
            Seq(Power(d), Sp, Minus, Sp, IndexedSum(i, Indices,
                new Formula.Floor(Seq(Power(d), Sp, Call("p", i)))))))));
    }

    private static Formula CostFormula()
    {
        var p = V("p"); var d = V("d");
        return Disp(All(p, Laws, Equal(Call("L", p), IndexedSum(d, Nat, Term(p, d)))));
    }

    private static Formula ResultFormula()
    {
        var p = V("p"); var i = V("i"); var d = V("d"); var t = V("t");
        var assumptions = And(All(i, Indices, Seq(D(0), Le, Call("p", i))),
            Equal(IndexedSum(i, Indices, Call("p", i)), D(1)));
        var bounds = And(Seq(D(0), Le, t), And(Seq(t, Le, new Formula.Fraction(D(1), D(5))),
            And(Seq(D(1, 6), Sp, t, Le, Call("L", p)),
                Seq(D(4, 8), Sp, t, Sp, Minus, Sp, D(6), Le, Call("L", p)))));
        return Disp(All(p, Laws, Imp(assumptions,
            And(Call("Summable", Lambda("d", Nat, Term(p, d))),
                All(t, Real, Imp(Equal(t, Call("min", p)), bounds))))));
    }
}
