using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class ParityConditionedMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform laws on the two parity fibers of a binary cube agree on every proper "
            + "marginal and differ exactly at the full product.",
        H("Parity-Conditioned Product Moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity-sign"),
                DeclarationHandle.Create(Prefix + "paritySign"),
                H("Binary coordinates as signs"),
                StatementSource.FromAuthor(ParitySignFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The binary value zero represents minus one and the binary value one "
                        + "represents plus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parity-fiber"),
                DeclarationHandle.Create(Prefix + "parityFiber"),
                H("The fiber of a prescribed total sign"),
                StatementSource.FromAuthor(ParityFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fiber consists of all binary strings whose coordinate-sign product "
                        + "equals the specified integer parity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parity-law"),
                DeclarationHandle.Create(Prefix + "parityLaw"),
                H("The uniform rational law on a parity fiber"),
                StatementSource.FromAuthor(ParityLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A point in the selected fiber receives mass 2 to the negative "
                        + "(d minus 1), and every point outside receives zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parity-marginal-mass"),
                DeclarationHandle.Create(Prefix + "parityMarginalMass"),
                H("Mass of a coordinate restriction"),
                StatementSource.FromAuthor(ParityMarginalMassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This finite sum is the mass of the event that a binary string agrees "
                        + "with y at every coordinate in A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parity-conditioned-moments"),
                DeclarationHandle.Create(Prefix + "parity_conditioned_moments"),
                H("Cardinality and product moments on one parity fiber"),
                StatementSource.FromAuthor(ParityConditionedMomentsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For d = k+1 and parity epsilon equal to minus one or plus one, the "
                            + "fiber has 2^k elements. Every nonempty proper-coordinate product "
                            + "sums to zero, while every full-coordinate product equals epsilon.")),
                    Paragraph(Text(
                        "The proper-moment cancellation pairs each string with the result of "
                            + "flipping one coordinate in A and one outside A. This is a "
                            + "fixed-point-free involution of the same parity fiber and negates "
                            + "the A-product. A single-coordinate flip bijects the two fibers, "
                            + "giving the cardinality after partitioning the full cube."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parity-conditioned-probability-form"),
                DeclarationHandle.Create(Prefix + "parity_conditioned_probability_form"),
                H("The two parity laws have identical proper marginals"),
                StatementSource.FromAuthor(ParityConditionedProbabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Both rational laws have total mass one. Every nonempty proper product "
                            + "has expectation zero under both laws, their full-product "
                            + "expectations are respectively minus one and plus one, and every "
                            + "proper marginal, including the empty marginal, is identical.")),
                    Paragraph(Text(
                        "The mass and moment clauses use the preceding parity-fiber calculation. "
                            + "For marginal equality, flipping one coordinate outside A is a "
                            + "bijection between the two fibers and preserves the restriction "
                            + "event on A."))),
                DescribeRole.Theorem))));

    private static Formula ParitySignFormula()
    {
        Formula b = F.Id("b");
        return Disp(Seq(
            Forall, Sp, b, Colon, Sp, Fin(D(2)), Comma, Sp,
            Call("paritySign", b), Sp, Eq, Sp,
            Call("ite", Equal(b, D(0)), NegativeOne(), D(1)), Dot));
    }

    private static Formula ParityFiberFormula()
    {
        Formula d = F.Id("d");
        Formula epsilon = Varepsilon;
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        return Disp(Seq(
            Forall, Sp, d, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            epsilon, Sp, InMacro, Sp, Integers(), Comma, RowBreak,
            Call("parityFiber", d, epsilon), Sp, Eq, Sp,
            Call("filter", Call("univ", Cube(d)),
                Seq(x, Sp, Mapsto, Sp,
                    Equal(ProductOver(i, Fin(d), Call("paritySign", Apply(x, i))), epsilon))),
            Dot));
    }

    private static Formula ParityLawFormula()
    {
        Formula d = F.Id("d");
        Formula epsilon = Varepsilon;
        Formula x = F.Id("x");
        Formula support = Call("parityFiber", d, epsilon);
        Formula mass = Inverse(Power(D(2), Difference(d, D(1))));
        return Disp(Seq(
            Forall, Sp, d, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            epsilon, Sp, InMacro, Sp, Integers(), Comma, Sp,
            x, Sp, InMacro, Sp, Cube(d), Comma, RowBreak,
            Call("parityLaw", d, epsilon, x), Sp, Eq, Sp,
            Call("ite", Member(x, support), mass, D(0)), Dot));
    }

    private static Formula ParityMarginalMassFormula()
    {
        Formula d = F.Id("d");
        Formula epsilon = Varepsilon;
        Formula subset = F.Id("A");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula i = F.Id("i");
        Formula agrees = Seq(
            Forall, Sp, i, Sp, InMacro, Sp, subset, Comma, Sp,
            Equal(Apply(x, i), Apply(y, i)));
        return Disp(Seq(
            Forall, Sp, d, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            epsilon, Sp, InMacro, Sp, Integers(), Comma, Sp,
            subset, Colon, Sp, Call("Finset", Fin(d)), Comma, Sp,
            y, Sp, InMacro, Sp, Cube(d), Comma, RowBreak,
            Call("parityMarginalMass", d, epsilon, subset, y), Sp, Eq, Sp,
            SumOver(x, Cube(d),
                Call("ite", Grp(agrees), Call("parityLaw", d, epsilon, x), D(0))), Dot));
    }

    private static Formula ParityConditionedMomentsFormula()
    {
        Formula k = F.Id("k");
        Formula d = Add(k, D(1));
        Formula epsilon = Varepsilon;
        Formula subset = F.Id("A");
        Formula x = F.Id("x");
        Formula i = F.Id("i");
        Formula fiber = Call("parityFiber", d, epsilon);
        Formula subsetProduct = ProductOver(
            i, subset, Call("paritySign", Apply(x, i)));
        Formula fullProduct = ProductOver(
            i, Fin(d), Call("paritySign", Apply(x, i)));
        Formula allowedParity = Seq(
            Open, Equal(epsilon, NegativeOne()), Close, Sp, Lor, Sp,
            Open, Equal(epsilon, D(1)), Close);
        Formula properMoment = Seq(
            Forall, Sp, subset, Colon, Sp, Call("Finset", Fin(d)), Comma, Sp,
            Nonempty(subset), Sp, Rightarrow, Sp,
            NotEqual(subset, F.Id("univ")), Sp, Rightarrow, RowBreak,
            SumOver(x, fiber, subsetProduct), Sp, Eq, Sp, D(0));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                epsilon, Sp, InMacro, Sp, Integers(), Comma),
            Seq(allowedParity, Sp, Rightarrow),
            Seq(Call("card", fiber), Sp, Eq, Sp, Power(D(2), k), Sp, Land),
            Seq(Open, properMoment, Close, Sp, Land),
            Seq(SumOver(x, fiber, fullProduct), Sp, Eq, Sp,
                Product(epsilon, Call("card", fiber)), Dot),
        ]));
    }

    private static Formula ParityConditionedProbabilityFormula()
    {
        Formula k = F.Id("k");
        Formula d = Add(k, D(1));
        Formula subset = F.Id("A");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula i = F.Id("i");
        Formula negative = NegativeOne();
        Formula positive = D(1);
        Formula subsetProduct = ProductOver(
            i, subset, Call("paritySign", Apply(x, i)));
        Formula fullProduct = ProductOver(
            i, Fin(d), Call("paritySign", Apply(x, i)));
        Formula negativeLaw = Call("parityLaw", d, negative, x);
        Formula positiveLaw = Call("parityLaw", d, positive, x);
        Formula masses = Seq(
            Open, SumOver(x, Cube(d), negativeLaw), Sp, Eq, Sp, D(1), Close,
            Sp, Land, Sp,
            Open, SumOver(x, Cube(d), positiveLaw), Sp, Eq, Sp, D(1), Close);
        Formula properMoments = Seq(
            Forall, Sp, subset, Colon, Sp, Call("Finset", Fin(d)), Comma, Sp,
            Nonempty(subset), Sp, Rightarrow, Sp,
            NotEqual(subset, F.Id("univ")), Sp, Rightarrow, RowBreak,
            Open, SumOver(x, Cube(d), Product(negativeLaw, subsetProduct)),
            Sp, Eq, Sp, D(0), Close, Sp, Land, RowBreak,
            Open, SumOver(x, Cube(d), Product(positiveLaw, subsetProduct)),
            Sp, Eq, Sp, D(0), Close);
        Formula negativeFull = Seq(
            SumOver(x, Cube(d), Product(negativeLaw, fullProduct)),
            Sp, Eq, Sp, negative);
        Formula positiveFull = Seq(
            SumOver(x, Cube(d), Product(positiveLaw, fullProduct)),
            Sp, Eq, Sp, positive);
        Formula marginalEquality = Seq(
            Forall, Sp, subset, Colon, Sp, Call("Finset", Fin(d)), Comma, Sp,
            NotEqual(subset, F.Id("univ")), Sp, Rightarrow, Sp,
            Forall, Sp, y, Sp, InMacro, Sp, Cube(d), Comma, RowBreak,
            Call("parityMarginalMass", d, negative, subset, y), Sp, Eq, Sp,
            Call("parityMarginalMass", d, positive, subset, y));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(Open, masses, Close, Sp, Land),
            Seq(Open, properMoments, Close, Sp, Land),
            Seq(Open, negativeFull, Close, Sp, Land),
            Seq(Open, positiveFull, Close, Sp, Land),
            Seq(Open, marginalEquality, Close, Dot),
        ]));
    }

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula Cube(Formula dimension) =>
        Power(Fin(D(2)), Fin(dimension));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula NegativeOne() => Seq(Minus, D(1));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Nonempty(Formula set) =>
        NotEqual(set, Emptyset);

    private static Formula Difference(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Inverse(Formula value) =>
        Power(Grp(value), NegativeOne());

    private static Formula ProductOver(Formula index, Formula set, Formula term) =>
        Seq(Prod, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);

    private static Formula SumOver(Formula index, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, set), Sp, term);
}
