using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.PellFamilies;

internal sealed class IntegralGeneralLinearLocalPeriodicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral general-linear updates are permutations with pure-periodic prime-power reductions.",
        H("Integral General-Linear Local Periodicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "integral-general-linear-update-is-prime-power-pure-periodic"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/PellFamilies/"
                        + "IntegralGeneralLinearLocalPeriodicity."
                        + "integral_general_linear_update_is_prime_power_pure_periodic"),
                H("Prime-power reductions of integral invertible updates are purely periodic"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The local state carrier is the d-coordinate vector space over ZMod(p^k). "
                            + "The update is constructed by mapping the entries of the given "
                            + "integral general-linear matrix into that quotient and applying "
                            + "the resulting matrix to a local state.")),
                    Paragraph(Text(
                        "General-linear base change preserves invertibility, so the displayed "
                            + "local update is bijective. On this finite carrier injectivity puts "
                            + "every initial state on a cycle, yielding a positive period whose "
                            + "periodicity law holds from time zero."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula dimension = F.Id("d");
        Formula prime = DefinitionDsl.Id("p");
        Formula exponent = DefinitionDsl.Id("k");
        Formula integerUpdate = F.Id("G");
        Formula modulus = F.Id("q");
        Formula reducedUpdate = F.Id("Gq");
        Formula update = F.Id("tau");
        Formula initial = F.Id("x");
        Formula state = F.Id("v");
        Formula period = F.Id("T");
        Formula time = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula modulusDefinition = new Formula.Power(prime, exponent);
        Formula index = Call("Fin", dimension);
        Formula localScalars = Call("ZMod", modulus);
        Formula localState = Call("Vector", localScalars, dimension);
        Formula integerGeneralLinear = Call("GL", index, integers);
        Formula reducedDefinition = Call("mapEntries", integerUpdate, localScalars);
        Formula updateDefinition = Seq(
            Open, state, Sp, Mapsto, Sp,
            Call("mulVec", reducedUpdate, state), Close);
        Formula orbitAt = Call("iterate", update, time, initial);
        Formula orbitShift = Call("iterate", update,
            Seq(time, Sp, Plus, Sp, period), initial);
        Formula purePeriodicity = Seq(
            Forall, Sp, initial, Sp, InMacro, Sp, localState, Comma, Sp,
            Exists, Sp, period, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            Forall, Sp, time, Sp, InMacro, Sp, naturals, Comma, Sp,
            orbitShift, Sp, Eq, Sp, orbitAt);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, dimension, Comma, Sp, prime, Comma, Sp, exponent,
                Sp, InMacro, Sp, naturals, Comma),
            Seq(
                integerUpdate, Colon, Sp, integerGeneralLinear, Comma, Sp,
                Call("Prime", prime), Sp, Rightarrow),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                modulus, Sp, Eq, Sp, modulusDefinition, Comma, Sp,
                reducedUpdate, Sp, Eq, Sp, reducedDefinition, Comma),
            Seq(
                update, Sp, Eq, Sp, updateDefinition, SemiSpace),
            Seq(
                Call("Bijective", update), Sp, Land, Sp, purePeriodicity, Dot),
        ]));
    }
}
