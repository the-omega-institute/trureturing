using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Radical;

internal sealed class GoldenRadicalDividedDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Radical/GoldenRadicalDividedDifference.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A genuine square-modulus lift in the fixed golden ring constructs a divided "
            + "geometric sum with an explicit quadratic equation and algebraic integrality.",
        H("Golden Radical Divided-Difference Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("radical-homogeneous-power-sum"),
                DeclarationHandle.Create(Prefix + "powerSum"),
                H("Homogeneous power sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural n and elements x,a of a commutative ring, powerSum(n,x,a) "
                        + "is the sum of x^i*a^(n-1-i) over 0<=i<n. Its value at n=0 is zero. "
                        + "This is the polynomial divided difference of X^n, with no division "
                        + "by x-a and with coincident arguments allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radical-second-divided-difference"),
                DeclarationHandle.Create(Prefix + "secondDifference"),
                H("Integral second divided difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "secondDifference(n,x,a) is the sum over 0<=i<n of "
                        + "a^(n-1-i)*powerSum(i,x,a). All coefficients are integers. "
                        + "Multiplication by x-a gives powerSum(n,x,a)-n*a^(n-1), "
                        + "including the n=0 and n=1 boundaries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radical-divided-power-sum"),
                DeclarationHandle.Create(Prefix + "dividedPowerSum"),
                H("Specified candidate integral element"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a field L, dividedPowerSum(n,x,a) is powerSum(n,x,a) divided by "
                        + "the natural-number cast of n. The public theorem explicitly "
                        + "requires positive n and characteristic zero. It never divides "
                        + "by x-a or by the lift witness b."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-radical-integral-certificate"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Explicit integral generator from a square-modulus golden lift"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "L is any characteristic-zero field and iota is a ring homomorphism "
                            + "from the existing GoldenInt ring into L. For n>0, a,b in "
                            + "GoldenInt and theta in L, assume theta^n=iota(phi) and the "
                            + "actual equality phi=a^n+n^2*b in GoldenInt. The defined y is "
                            + "then integral over the integers and satisfies both displayed "
                            + "identities. No integral-basis or local-field theorem is "
                            + "assumed in the formal argument.")),
                    Paragraph(Text(
                        "The proof sums the classical difference-of-powers identity twice. "
                            + "It obtains (theta-iota(a))*y=n*iota(b) and the quadratic "
                            + "equation, cancelling only the nonzero scalar n. Golden "
                            + "integers satisfy monic integer polynomials; theta is integral "
                            + "because its positive power is. Hence the second-difference "
                            + "coefficient is integral, and integrality transitivity through "
                            + "the explicit monic quadratic proves integrality of y.")),
                    Paragraph(Text(
                        "The quadratic coefficients may contain theta. This is not a "
                            + "degree-at-most-two assertion over the golden number field. "
                            + "The lift hypothesis is not proved for an unknown WSS prime. "
                            + "The separate sharp n*rad(n) criterion and the full class-field "
                            + "statements are ordinary mathematical deductions in the "
                            + "existing WSS dossier, not further Lean conclusions here."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ResultFormula()
    {
        var l = V("L");
        var g = V("GoldenInt");
        var n = V("n");
        var a = V("a");
        var b = V("b");
        var theta = V("theta");
        Formula Image(Formula x) => Call("iota", x);
        var nl = Call("NatCast", l, n);
        var ng = Call("NatCast", g, n);
        var y = Call("dividedPowerSum", n, theta, Image(a));
        var first = Call("Eq", Call("mul", Call("sub", theta, Image(a)), y),
            Call("mul", nl, Image(b)));
        var second = Call("Eq", Pow(y, D(2)),
            Call("add", Call("mul", Pow(Image(a), Call("Nat.sub", n, D(1))), y),
                Call("mul", Image(b), Call("secondDifference", n, theta, Image(a)))));
        var conclusion = Call("And", first,
            Call("And", second, Call("IsIntegral", V("Int"), y)));
        var root = Call("Eq", Pow(theta, n), Image(V("phi")));
        var lift = Call("Eq", V("phi"),
            Call("add", Pow(a, n), Call("mul", Pow(ng, D(2)), b)));
        var premises = Call("And", Call("Lt", D(0), n), Call("And", root, lift));
        var quantified = All("iota", Call("RingHom", g, l),
            All("n", V("Nat"), All("a", g, All("b", g,
                All("theta", l, Call("Implies", premises, conclusion))))));
        return Disp(All("L", V("Type"),
            Call("Implies", Call("And", Call("Field", l), Call("CharZero", l)),
                quantified)));
    }
}
