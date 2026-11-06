using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.AlgebraicSeries;

internal sealed class HannaA3958InfinitudeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/AnalyticClosure/hanna2026a395835");

    public DocumentDefinition Create()
    {
        var nodes = new List<DocumentBlock>
        {
            Node("Shared.SeriesEquation", "The integral formal-series equation", EquationFormula(),
                SourceName(395835) + " OEIS NAME, revision 48; no printed page number. F is an integral formal power series, x is PowerSeries.X, and 2*n is an ordinary multiplicative exponent.", true),
            Node("Shared.DefinedThrough", "Every required earlier parameter is defined", PrefixFormula(),
                "The source stopping sentence is: Should no such M exist for some n, then there are no further terms and this sequence would be finite. OEIS A395835 NAME, revision 48; no printed page number. DefinedThrough N requires every natural parameter from 2 through N. IsLeast selects the first strictly negative coefficient.", true)
        };
        foreach (var number in new[] {395835, 395836, 395837, 395838})
        {
            var family = "A" + number;
            nodes.Add(Node(family + "." + Leaf(number, "Term"), "The " + family + " term relation", TermFormula(number),
                SourceName(number) + " OEIS NAME; no printed page number. The parameter n is natural and a is integral. " +
                (number == 395838
                    ? "The forward difference is M(n+1)-M(n). The published table prepends M(2) and shifts this tail by one place; this preserves finite versus infinite length. DefinedThrough(n+1) requires both terms and every preceding term."
                    : "DefinedThrough n enforces the stopping rule. " + (number == 395837 ? "M-1 is natural predecessor subtraction. The equation forces the constant coefficient to be one, so the first negative index is positive." : "The index M is natural and is coerced to the integers when read as a value.")), true));
            nodes.Add(Node(family + "." + Leaf(number, "claim"), "The " + family + " infinitude conjecture",
                Disp(Iff(Q(family, Leaf(number, "claim")), ClaimBody(number))),
                "Conjecture: this sequence is infinite. OEIS " + family + " COMMENTS; no printed page number. This means an infinite domain of defined indices n, with an integral value a at each such index. It imposes no distinctness condition on the values.", true));
            nodes.Add(Node(family + "." + Leaf(number, "result"), "The " + family + " domain is infinite", Disp(ClaimBody(number)),
                "For every n at least two the unique integral solution has a negative coefficient. Well ordering gives its first negative index, hence every required prefix and each of the four readouts exists. These are four equivalent infinitude assertions with one shared existence proof. Assuming nonnegative coefficients forces a finite positive radius R and a bounded increasing real sum with limit L. With t=R*L^2, the numerator 1-t+(2*n-1)*t^n is positive. The rational map t/(1+t-t^n)^2 therefore has a local analytic inverse at the positive boundary, contradicting the Pringsheim obstruction. The related questions are OEIS A395835, A395836, A395837 and A395838.", false));
        }
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every integral solution of Hanna's equation for n at least two has a negative coefficient, giving infinite defined domains for the four associated sequences.",
            H("Hanna's first negative coefficients exist for every parameter"), Blocks([.. nodes])));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create("hanna-" + name.Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), literature ? DescribeRole.Definition : DescribeRole.Theorem);

    private static string Leaf(int number, string name) =>
        number == 395835 && name != "Term" ? name : name + (number - 395000);

    private static string SourceName(int number) => number switch
    {
        395835 => "Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = M where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite.",
        395836 => "Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = abs( [x^M] F(n,x) ) where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite.",
        395837 => "Define F(n,x) as the power series in x satisfying F(n,x) = 1 + x*F(n,x)^2 - x^n*F(n,x)^(2*n), then for n >= 2, a(n) = [x^(M-1)] F(n,x) where x^M is the first power of x with a negative coefficient in F(n,x). Should no such M exist for some n, then there are no further terms and this sequence would be finite.",
        _ => "First differences of A395835."
    };

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Int => Seq(Mathbb, Grp(V("Z")));
    private static Formula PS => Call("PowerSeries", Int);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Colon, Sp, Int));
    private static Formula Equation(Formula n, Formula f) => App(Q("Shared", "SeriesEquation"), n, f);
    private static Formula Defined(Formula n) => App(Q("Shared", "DefinedThrough"), n);
    private static Formula Coeff(Formula m, Formula f) => App(Q("PowerSeries", "coeff"), m, f);
    private static Formula First(Formula f, Formula m) => Call("IsLeast",
        Seq(OpenBrace, V("m"), Colon, Sp, Nat, Sp, Mid, Sp, Lt(Coeff(V("m"), f), D(0)), CloseBrace), m);

    private static Formula EquationFormula()
    {
        Formula n = V("n"), f = V("F"), x = Q("PowerSeries", "X");
        return Disp(All("n", Nat, All("F", PS, Iff(Equation(n, f), Equal(f,
            Subtract(Add(D(1), Multiply(x, Pow(f, D(2)))), Multiply(Pow(x, n), Pow(f, Multiply(D(2), n)))))))));
    }

    private static Formula PrefixBody(Formula upper)
    {
        Formula witness = Ex("F", PS, And(Equation(V("n"), V("F")),
            Ex("M", Nat, First(V("F"), V("M")))));
        return All("n", Nat, Imp(Le(D(2), V("n")), Imp(Le(V("n"), upper), witness)));
    }
    private static Formula PrefixFormula() => Disp(All("N", Nat, Iff(Defined(V("N")), PrefixBody(V("N")))));

    private static Formula TermBody(int number)
    {
        Formula n = V("n"), a = V("a"), f = V("F"), m = V("M");
        Formula tail;
        if (number == 395838)
        {
            Formula g = V("G"), next = V("N");
            tail = Ex("F", PS, Ex("G", PS, Ex("M", Nat, Ex("N", Nat,
                And(Equation(n, f), And(First(f, m), And(Equation(Add(n, D(1)), g),
                    And(First(g, next), Equal(a, Subtract(Cast(next), Cast(m)))))))))));
        }
        else
        {
            Formula value = number == 395835 ? Cast(m) : number == 395836
                ? new Formula.Absolute(Coeff(m, f)) : Coeff(Subtract(m, D(1)), f);
            tail = Ex("F", PS, Ex("M", Nat, And(Equation(n, f), And(First(f, m), Equal(a, value)))));
        }
        return And(Le(D(2), n), And(Defined(number == 395838 ? Add(n, D(1)) : n), tail));
    }
    private static Formula TermFormula(int number) => Disp(All("n", Nat, All("a", Int,
        Iff(App(Q("A" + number, Leaf(number, "Term")), V("n"), V("a")), TermBody(number)))));
    private static Formula ClaimBody(int number) => App(Q("Set", "Infinite"),
        Seq(OpenBrace, V("n"), Colon, Sp, Nat, Sp, Mid, Sp,
            Ex("a", Int, App(Q("A" + number, Leaf(number, "Term")), V("n"), V("a"))), CloseBrace));
}
