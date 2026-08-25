using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class HorizontalJointKernelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Congruence/HorizontalJointKernel.horizontal_joint_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family of positive prime-power residue channels has product-modulus kernel.",
        H("Horizontal Joint Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("horizontal-joint-kernel"),
                DeclarationHandle.Create(Declaration),
                H("The joint residue kernel is divisibility by the product modulus"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite set of natural numbers, require every member of S "
                            + "to be prime, and assign each selected prime a positive natural "
                            + "precision. The readout is constructed from the integer reduction "
                            + "channel modulo p raised to that precision at every p in S.")),
                    Paragraph(Text(
                        "Two integers have equal joint readouts exactly when their difference "
                            + "is divisible by the product of the selected prime powers. "
                            + "Pairwise coprimality of distinct selected primes combines the "
                            + "component divisibilities, while every component modulus divides "
                            + "the product for the reverse implication.")),
                    Paragraph(Text(
                        "The declaration uses the existing jointReadout family primitive and "
                            + "the library equivalence between equality in ZMod and divisibility "
                            + "of an integer difference. It introduces no parallel readout or "
                            + "product-modulus definition."))),
                DescribeRole.Theorem))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() =>
        Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula PrecisionAt(Formula precision, Formula prime) =>
        Seq(precision, Open, prime, Close);

    private static Formula PrimePower(Formula precision, Formula prime) =>
        Seq(prime, Caret, Grp(PrecisionAt(precision, prime)));

    private static Formula JointReading(
        Formula primeSet,
        Formula precision,
        Formula value)
    {
        Formula prime = F.Id("p");
        Formula integer = F.Id("z");
        Formula channel = Seq(
            integer, Sp, Mapsto, Sp,
            new Formula.Modulo(integer, PrimePower(precision, prime)));
        Formula channels = Seq(
            Open, channel, Close, Underscore,
            Grp(prime, Sp, InMacro, Sp, primeSet));
        return Call("jointReadout", channels, value);
    }

    private static Formula KernelFormula()
    {
        Formula primeSet = F.Id("S");
        Formula precision = Kappa;
        Formula prime = F.Id("p");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula finiteNaturals = Call("Finset", NaturalNumbers());
        Formula positiveNaturals = Call("PNat");
        Formula allSelectedPrime = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, primeSet, Comma, Sp,
            Call("Prime", prime));
        Formula modulusProduct = Seq(
            Prod, Underscore, Grp(prime, Sp, InMacro, Sp, primeSet), Sp,
            PrimePower(precision, prime));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            primeSet, Colon, Sp, finiteNaturals, Comma, Quad, Sp,
            allSelectedPrime, Comma, RowBreak, Grp(),
            precision, Colon, Sp, primeSet, Sp, To, Sp, positiveNaturals, Comma, Quad, Sp,
            left, Comma, Sp, right, Sp, InMacro, Sp, Integers(), Comma, RowBreak, Grp(),
            JointReading(primeSet, precision, left), Sp, Eq, Sp,
            JointReading(primeSet, precision, right), RowBreak, Grp(),
            Iff, Sp, modulusProduct, Sp, Mid, Sp,
            Open, left, Sp, Minus, Sp, right, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
