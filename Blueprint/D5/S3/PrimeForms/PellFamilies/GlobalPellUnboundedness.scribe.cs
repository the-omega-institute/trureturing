using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.PellFamilies;

internal sealed class GlobalPellUnboundednessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete Pell orbit is globally unbounded and locally pure-periodic.",
        H("Global and Local Pell Behavior"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sqrt-three-pell-orbit-is-unbounded"),
                DeclarationHandle.Create(Prefix + "sqrt_three_pell_orbit_is_unbounded"),
                H("A concrete Pell orbit is globally unbounded"),
                StatementSource.FromAuthor(UnboundedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the multiplication matrix of 2 + sqrt(3) and start at "
                            + "the integral seed (1, 0). Its second coordinate is the "
                            + "standard Pell y-sequence from pinned Mathlib.")),
                    Paragraph(Text(
                        "Mathlib's lower bound n <= y_n supplies a coordinate above "
                            + "every prescribed natural bound, without a limit or a "
                            + "new induction proving growth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-one-pell-orbit-is-not-unbounded"),
                DeclarationHandle.Create(Prefix + "unit_one_pell_orbit_is_not_unbounded"),
                H("The unit one orbit is a necessary degeneracy"),
                StatementSource.FromAuthor(UnitOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For unit coordinates (1, 0), the Pell multiplication matrix is "
                        + "the identity. Starting from the nonzero seed (1, 0) therefore "
                        + "gives a constant orbit, which is not unbounded."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "global-unboundedness-and-prime-power-local-periodicity"),
                DeclarationHandle.Create(
                    Prefix + "global_unboundedness_and_prime_power_local_periodicity"),
                H("Global growth and local cycles coexist"),
                StatementSource.FromAuthor(CompatibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first conjunct is the global unboundedness result for the "
                            + "single named integer matrix orbit.")),
                    Paragraph(Text(
                        "For every prime p and exponent k, reduction of that same orbit "
                            + "modulo p^k is identified with the mapped matrix orbit. The "
                            + "existing local Pell periodicity theorem then gives a positive "
                            + "pure period, including p = 2 and k = 0."))),
                DescribeRole.Theorem))));

    private static Formula UnboundedFormula()
    {
        Formula pellOrbit = F.Id("u");
        Formula bound = F.Id("N");
        Formula time = F.Id("n");
        Formula coordinate = F.Id("i");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finTwo = Call("Fin", D(2));
        Formula concreteOrbit = Call("PellOrbit", D(3), D(2), D(1),
            Seq(Open, D(1), Comma, Sp, D(0), Close));
        return Disp(Seq(
            pellOrbit, Sp, Eq, Sp, concreteOrbit, Comma, Sp,
            Forall, Sp, bound, Sp, InMacro, Sp, naturals, Comma, Sp,
            Exists, Sp, time, Sp, InMacro, Sp, naturals, Comma, Sp,
            Exists, Sp, coordinate, Sp, InMacro, Sp, finTwo, Comma, Sp,
            bound, Sp, Lt, Sp,
            Seq(Grp(pellOrbit, Underscore, Grp(time)), Underscore, Grp(coordinate)), Dot));
    }

    private static Formula UnitOneFormula()
    {
        Formula constantOrbit = Call("PellOrbit", D(3), D(1), D(0),
            Seq(Open, D(1), Comma, Sp, D(0), Close));
        return Disp(Seq(Neg, Call("OrbitUnbounded", constantOrbit), Dot));
    }

    private static Formula CompatibilityFormula()
    {
        Formula orbit = F.Id("u");
        Formula prime = DefinitionDsl.Id("p");
        Formula exponent = DefinitionDsl.Id("k");
        Formula period = F.Id("T");
        Formula time = F.Id("n");
        Formula coordinate = F.Id("i");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula modulus = new Formula.Power(prime, exponent);
        Formula concreteOrbit = Call("PellOrbit", D(3), D(2), D(1),
            Seq(Open, D(1), Comma, Sp, D(0), Close));
        Formula reducedValue = Call("mod",
            Seq(Grp(orbit, Underscore, Grp(time)), Underscore, Grp(coordinate)),
            modulus);
        Formula periodicity = Seq(
            Forall, Sp, time, Sp, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, coordinate, Sp, InMacro, Sp, Call("Fin", D(2)), Comma, Sp,
            Call("mod",
                Seq(Grp(orbit, Underscore, Grp(Seq(time, Sp, Plus, Sp, period))),
                    Underscore, Grp(coordinate)), modulus),
            Sp, Eq, Sp, reducedValue);
        return Disp(Seq(
            orbit, Sp, Eq, Sp, concreteOrbit, Comma, Sp,
            Call("OrbitUnbounded", orbit), Sp, Land, Sp,
            Forall, Sp, prime, Comma, Sp, exponent, Sp, InMacro, Sp, naturals,
            Comma, Sp, Call("Prime", prime), Sp, Rightarrow, Sp,
            Exists, Sp, period, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp, periodicity, Dot));
    }
}
