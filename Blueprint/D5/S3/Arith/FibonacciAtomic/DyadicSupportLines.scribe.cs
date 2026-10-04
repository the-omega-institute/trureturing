using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class DyadicSupportLinesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/DyadicSupportLines.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Indices(byte n) => Call("Fin", D(n));
    private static Formula Finite(Formula type, Formula body) =>
        All(type, V("Type"), Seq(OpenBracket, Call("Fintype", type), CloseBracket, Comma, Sp, body));
    private static Formula Laws(byte n) => Seq(Indices(n), Sp, To, Sp, Real);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Power(Formula d) => new Formula.Power(D(2), d);
    private static Formula Term(Formula p, Formula d) =>
        new Formula.Fraction(Call("R", p, d), Power(d));
    private static Formula IndexedSum(Formula i, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, domain)), body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine supporting inequalities for the classical dyadic cost on the five-outcome real simplex.",
        H("Dyadic Cost Support Lines"),
        Blocks(
            Describe.Lean(DescribeId.Create("residual"), DeclarationHandle.Create(Prefix + "residual"),
                H("Dyadic residual"), StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                Blocks(Paragraph(Text("R(p,d) counts unassigned dyadic cylinders algebraically. "
                    + "The floor is the integer floor. For a nonnegative real probability vector "
                    + "with m coordinates summing to one, R(p,d) is an integer between zero "
                    + "and m-1. Zero coordinates and terminating dyadic expansions are included."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cost"), DeclarationHandle.Create(Prefix + "cost"),
                H("Classical dyadic tail cost"), StatementSource.FromAuthor(CostFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                Blocks(Paragraph(Text("L(p) is the real infinite sum of these normalized residuals. "
                    + "The geometric bound (m-1) divided by 2 to the power d gives summability "
                    + "on each finite simplex. The series expression is the classical "
                    + "Knuth-Yao DDG cost recalled by Lumbroso, Section 2.1. The support theorem "
                    + "below concerns this numerical series. Both definitions accept arbitrary finite "
                    + "real vectors. Lean takes an unsummable real tsum to be zero; values outside "
                    + "the probability simplex do not represent sampling costs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("support-bounds"), DeclarationHandle.Create(Prefix + "result"),
                H("Five-outcome support lines"), StatementSource.FromAuthor(ResultFormula(5, D(1, 6), D(4, 8), D(6))),
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
        var p = V("p"); var i = V("i"); var d = V("d"); var type = V("I");
        var laws = Seq(type, Sp, To, Sp, Real);
        return Disp(Finite(type, All(p, laws, All(d, Nat, Equal(Call("R", p, d),
            Seq(Power(d), Sp, Minus, Sp, IndexedSum(i, type,
                new Formula.Floor(Seq(Power(d), Sp, Call("p", i))))))))));
    }

    private static Formula CostFormula()
    {
        var p = V("p"); var d = V("d"); var type = V("I");
        var laws = Seq(type, Sp, To, Sp, Real);
        return Disp(Finite(type, All(p, laws, Equal(Call("L", p), IndexedSum(d, Nat, Term(p, d))))));
    }

    private static Formula ResultFormula(byte n, Formula first, Formula second, Formula intercept)
    {
        var p = V("p"); var i = V("i"); var d = V("d"); var t = V("t");
        var assumptions = And(Par(All(i, Indices(n), Seq(D(0), Sp, Le, Sp, Call("p", i)))),
            Equal(IndexedSum(i, Indices(n), Call("p", i)), D(1)));
        var bounds = And(Seq(D(0), Sp, Le, Sp, t),
            And(Seq(t, Sp, Le, Sp, new Formula.Fraction(D(1), D(n))),
            And(Seq(first, Sp, t, Sp, Le, Sp, Call("L", p)),
                Seq(second, Sp, t, Sp, Minus, Sp, intercept, Sp, Le, Sp, Call("L", p)))));
        return Disp(All(p, Laws(n), Imp(assumptions,
            And(Call("Summable", Seq(d, Colon, Sp, Nat, Sp, Mapsto, Sp, Term(p, d))),
                All(t, Real, Imp(Equal(t, Call("min", p)), bounds))))));
    }
}
