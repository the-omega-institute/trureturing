using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PrimeSquareThickFactorObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/PrimeSquareThickFactorObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two reduced factors that both have a double root at one cannot multiply to "
            + "X^p-1 over ZMod(p^2). This excludes every lift of each intermediate "
            + "power of X-1, and includes a boundary witness at p=3.",
        H("Multiple-Root Factors Modulo a Prime Square"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("thick-factor-reduction"),
                DeclarationHandle.Create(Prefix + "reduction"),
                H("The coefficient reduction homomorphism"),
                StatementSource.FromAuthor(ReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural p, reduction p is the canonical ring homomorphism "
                        + "ZMod(p^2) to ZMod(p), constructed by ZMod.castHom using p dividing p^2. "
                        + "On elements it is ZMod.cast. The product of any two elements in its "
                        + "kernel is zero: integer representatives are both multiples of p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thick-factor-product-obstruction"),
                DeclarationHandle.Create(Prefix + "no_thick_product"),
                H("Both reduced factors cannot be double at one"),
                StatementSource.FromAuthor(ProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quantifiers range over natural p,d,e and polynomials f,g over "
                        + "ZMod(p^2). The hypotheses are primality of p, d and e at least two, "
                        + "and the displayed equalities for the coefficientwise reductions. "
                        + "Those equalities put the values and first derivatives of both "
                        + "factors at one in the reduction kernel. The product rule makes "
                        + "the derivative of f*g at one zero, whereas the derivative of "
                        + "X^p-1 at one is p, which is nonzero modulo p^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thick-factor-intermediate-obstruction"),
                DeclarationHandle.Create(Prefix + "intermediate_factor_not_dvd"),
                H("Every intermediate reduced multiplicity is excluded"),
                StatementSource.FromAuthor(IntermediateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime p, natural d with 2 <= d and d+2 <= p, and polynomial "
                        + "f whose reduction is (X-1)^d, f does not divide X^p-1. Monicity "
                        + "is not required. If a cofactor existed, reduction and Frobenius "
                        + "would give (X-1)^d * map(g) = (X-1)^p over the field ZMod(p). "
                        + "Cancellation determines map(g) as (X-1)^(p-d), whose multiplicity "
                        + "is at least two. The product obstruction then applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thick-factor-quadratic-obstruction"),
                DeclarationHandle.Create(Prefix + "quadratic_lift_not_dvd"),
                H("No quadratic lift works for a prime at least five"),
                StatementSource.FromAuthor(QuadraticFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every polynomial over ZMod(p^2) reducing to (X-1)^2 is excluded "
                            + "when p is prime and 5 <= p. The conclusion quantifies over "
                            + "all lifted coefficients, including coefficients other than "
                            + "the unchanged pair -2 and 1.")),
                    Paragraph(Text(
                        "This applies to the proposed multiple-root quadratic lift in "
                            + "Shi, Wang, Bouazzaoui, Kim and Sole, Second order Recurrences, "
                            + "quadratic number fields and cyclic codes, arXiv:2603.25343v1, "
                            + "section 4.3. It concerns that construction. The separable "
                            + "golden polynomial X^2-X-1 at primes different from five has "
                            + "a different reduction. No Wall-Sun-Sun existence or "
                            + "nonexistence statement follows from this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thick-factor-cubic-boundary"),
                DeclarationHandle.Create(Prefix + "cubic_boundary_lift"),
                H("The excluded endpoint has a genuine factor"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the polynomial ring over ZMod(9), X^2+X+1 divides X^3-1, with "
                        + "cofactor X-1. Here the cofactor has only a simple root after "
                        + "reduction, so the double-root product obstruction does not "
                        + "apply. The displayed conclusion is this exact divisibility."))),
                DescribeRole.Theorem))));

    private static Formula Id(string x) => F.Id(x);
    private static Formula NatType() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Call(string name, params Formula[] xs)
    {
        var result = new List<Formula> { Operatorname, Grp(Id(name)), Open };
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(xs[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(v), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula P() => Id("p");
    private static Formula RingType() => Call("ZMod", Pow(P(), Id("2")));
    private static Formula PolyType() => Call("Polynomial", RingType());
    private static Formula Reduced(string f) => Call("Polynomial.map", Id(f), Call("reduction", P()));
    private static Formula RootPower(Formula d) => Pow(Call("sub", Id("X"), Id("1")), d);
    private static Formula ReturnPolynomial() => Call("sub", Pow(Id("X"), P()), Id("1"));
    private static Formula NotDivisor() => Call("Not", Call("Divides", Id("f"), ReturnPolynomial()));

    private static Formula ReductionFormula() => Disp(All("p", NatType(),
        All("z", RingType(), Eqn(Call("reduction", P(), Id("z")), Call("ZMod.cast", Id("z"))))));

    private static Formula ProductFormula() => Disp(All("p", NatType(),
        All("d", NatType(), All("e", NatType(), All("f", PolyType(), All("g", PolyType(),
            Call("Implies", Call("And", Call("Nat.Prime", P()),
                Call("Le", Id("2"), Id("d")), Call("Le", Id("2"), Id("e")),
                Eqn(Reduced("f"), RootPower(Id("d"))), Eqn(Reduced("g"), RootPower(Id("e")))),
                Call("Not", Eqn(Call("mul", Id("f"), Id("g")), ReturnPolynomial())))))))));

    private static Formula IntermediateFormula() => Disp(All("p", NatType(),
        All("d", NatType(), All("f", PolyType(),
            Call("Implies", Call("And", Call("Nat.Prime", P()),
                Call("Le", Id("2"), Id("d")), Call("Le", Call("add", Id("d"), Id("2")), P()),
                Eqn(Reduced("f"), RootPower(Id("d")))), NotDivisor())))));

    private static Formula QuadraticFormula() => Disp(All("p", NatType(), All("f", PolyType(),
        Call("Implies", Call("And", Call("Nat.Prime", P()), Call("Le", Id("5"), P()),
            Eqn(Reduced("f"), RootPower(Id("2")))), NotDivisor()))));

    private static Formula BoundaryFormula() => Disp(Call("DividesIn", Call("Polynomial", Call("ZMod", Id("9"))),
        Call("add", Call("add", Pow(Id("X"), Id("2")), Id("X")), Id("1")),
        Call("sub", Pow(Id("X"), Id("3")), Id("1"))));
}
