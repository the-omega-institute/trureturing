using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class RationalFiniteValuationKernelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/Embeddings/RationalFiniteValuationKernel."
            + "rational_finite_valuation_kernel_and_sign_recovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational prime coordinates leave exactly a sign ambiguity.",
        H("Rational Finite-Valuation Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-finite-valuation-kernel-and-sign-recovery"),
            DeclarationHandle.Create(Declaration),
            H("Finite valuations have kernel plus or minus one"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is the unit group of the rationals, so zero is excluded exactly "
                        + "as required by the finite prime-valuation profile. The displayed profile "
                        + "takes rational absolute value, packages it as a positive rational unit, "
                        + "and applies the canonical inverse signed-prime equivalence.")),
                Paragraph(Text(
                    "Equality of profiles therefore identifies absolute values and leaves only "
                        + "the two sign choices. The second public clause identifies the full "
                        + "kernel as one and minus one, rather than merely proving containment.")),
                Paragraph(Text(
                    "The final public clause adds equality of the archimedean sign. Opposite "
                        + "rational values then have opposite nonzero signs, so the remaining "
                        + "ambiguity is eliminated and the rationals are equal."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rationalUnits = F.Id("RatUnits");
        Formula ledger = F.Id("SignedPrimeLedger");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula q = F.Id("q");
        Formula z = F.Id("z");
        Formula profile = F.Id("nu");

        Formula Profile(Formula value) => Apply(profile, value);
        Formula Sign(Formula value) => Call("sign", value);
        Formula CanonicalProfile(Formula value) =>
            Invoke(
                Qualified(F.Id("primeExponentEquivPositiveRational"), "symm"),
                Invoke(
                    Qualified(F.Id("Additive"), "ofMul"),
                    Invoke(
                        Qualified(F.Id("Units"), "mk0"),
                        Invoke(Qualified(F.Id("Rat"), "nnabs"), value),
                        Call("nonzero", value))));

        Formula ambiguity = Seq(
            Profile(x), Sp, Eq, Sp, Profile(y), Sp, Rightarrow, Sp,
            Open, x, Sp, Eq, Sp, y, Sp, Lor, Sp, x, Sp, Eq, Sp, Minus, y, Close);
        Formula exactKernel = Seq(
            Forall, Sp, z, InMacro, Sp, rationalUnits, Comma, Sp,
            Profile(z), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            Open, z, Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            z, Sp, Eq, Sp, Minus, D(1), Close);
        Formula signedRecovery = Seq(
            Profile(x), Sp, Eq, Sp, Profile(y), Sp, Land, Sp,
            Sign(x), Sp, Eq, Sp, Sign(y), Sp, Rightarrow, Sp,
            x, Sp, Eq, Sp, y);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x, Comma, Sp, y, InMacro, Sp, rationalUnits, Comma,
            RowBreak, Grp(),
            F.Id("let"), Sp, profile, Colon, Sp, rationalUnits, Sp, To, Sp, ledger,
            Comma, Sp, Forall, Sp, q, Comma, Sp,
            Profile(q), Sp, Eq, Sp, CanonicalProfile(q), Comma,
            RowBreak, Grp(),
            Open, ambiguity, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, exactKernel, Close,
            RowBreak, Grp(), Land, RowBreak, Grp(),
            Open, signedRecovery, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Qualified(Formula owner, string member) =>
        Seq(owner, Dot, F.Id(member));

    private static Formula Invoke(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
