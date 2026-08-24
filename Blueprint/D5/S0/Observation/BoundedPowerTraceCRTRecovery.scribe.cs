using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Observation;

internal sealed class BoundedPowerTraceCRTRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A CRT image modulo a product wider than a known trace interval uniquely recovers the bounded matrix power trace.",
        H("Bounded Power-Trace Recovery from a CRT Image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-integer-unique-of-modulus"),
                DeclarationHandle.Create(
                    "D5/S0/Observation/BoundedPowerTraceCRTRecovery."
                        + "bounded_int_unique_of_mod"),
                H("A wide modulus separates bounded integers"),
                StatementSource.FromAuthor(BoundedIntegerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If M is strictly larger than twice B, reduction modulo M is injective "
                            + "on the integers whose absolute values are strictly below B. Thus "
                            + "two integers in that open interval with the same residue are equal.")),
                    Paragraph(Text(
                        "Indeed, their difference has absolute value below M and is divisible by "
                            + "M. The only such multiple of M is zero, which forces the original "
                            + "integers to coincide."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("power-trace-unique-of-crt-image"),
                DeclarationHandle.Create(
                    "D5/S0/Observation/BoundedPowerTraceCRTRecovery."
                        + "power_trace_unique_of_crt_image"),
                H("A wide CRT image uniquely determines a bounded power trace"),
                StatementSource.FromAuthor(PowerTraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A and C be square integer matrices on the same finite index type. "
                            + "For any natural exponent j, suppose both jth-power traces lie "
                            + "strictly between -B and B and the product modulus M exceeds 2B. "
                            + "Equality of their assembled CRT images then forces the two traces "
                            + "to be equal.")),
                    Paragraph(Text(
                        "The result is a uniqueness statement after the component residues have "
                            + "already been assembled into one residue modulo M. It neither "
                            + "constructs that CRT assembly nor recovers the matrices themselves; "
                            + "it recovers only the specified power trace."))),
                DescribeRole.Theorem))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() =>
        Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula MatrixSpace(Formula index) =>
        Call("Matrix", index, index, Integers());

    private static Formula PowerTrace(Formula matrix, Formula exponent) =>
        Call("tr", Seq(matrix, Caret, Grp(exponent)));

    private static Formula CrtImage(Formula modulus, Formula value) =>
        Call("crtImage", modulus, value);

    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(
            left, Sp, Equiv, Sp, right, Sp,
            Open, Operatorname, Grp(F.Id("mod")), Sp, modulus, Close);

    private static Formula BoundedIntegerFormula()
    {
        Formula modulus = F.Id("M");
        Formula bound = F.Id("B");
        Formula left = F.Id("m");
        Formula right = F.Id("n");

        return Disp(Seq(
            Forall, Sp, modulus, Comma, Sp, bound, Sp, InMacro, Sp,
            NaturalNumbers(), Comma, Sp,
            Forall, Sp, left, Comma, Sp, right, Sp, InMacro, Sp,
            Integers(), Comma, Sp,
            Open,
            D(2), Sp, Times, Sp, bound, Sp, Lt, Sp, modulus, Sp, Land, Sp,
            new Formula.Absolute(left), Sp, Lt, Sp, bound, Sp, Land, Sp,
            new Formula.Absolute(right), Sp, Lt, Sp, bound, Sp, Land, Sp,
            Congruent(left, right, modulus),
            Close, Sp, Rightarrow, Sp,
            left, Sp, Eq, Sp, right, Dot));
    }

    private static Formula PowerTraceFormula()
    {
        Formula index = F.Id("d");
        Formula modulus = F.Id("M");
        Formula bound = F.Id("B");
        Formula exponent = F.Id("j");
        Formula first = F.Id("A");
        Formula second = F.Id("C");
        Formula firstTrace = PowerTrace(first, exponent);
        Formula secondTrace = PowerTrace(second, exponent);

        return Disp(Seq(
            Forall, Sp, index, Colon, Sp, TypeUniverse(), Comma, Sp,
            Forall, Sp, modulus, Comma, Sp, bound, Comma, Sp, exponent,
            Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            Forall, Sp, first, Comma, Sp, second, Sp, InMacro, Sp,
            MatrixSpace(index), Comma, Sp,
            Open,
            Call("Fintype", index), Sp, Land, Sp,
            D(2), Sp, Times, Sp, bound, Sp, Lt, Sp, modulus, Sp, Land, Sp,
            new Formula.Absolute(firstTrace), Sp, Lt, Sp, bound, Sp, Land, Sp,
            new Formula.Absolute(secondTrace), Sp, Lt, Sp, bound, Sp, Land, Sp,
            CrtImage(modulus, firstTrace), Sp, Eq, Sp,
            CrtImage(modulus, secondTrace),
            Close, Sp, Rightarrow, Sp,
            firstTrace, Sp, Eq, Sp, secondTrace, Dot));
    }
}
