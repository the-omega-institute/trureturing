using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class CrtNilpotentAbelianVictoryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/PrimePowers/CrtNilpotentAbelianVictory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Additive ZMod has a Sylow decomposition that does not extend to all finite groups.",
        H("CRT as a Nilpotent Abelian Victory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zmod-additive-group-prime-power-decomposable"),
                DeclarationHandle.Create(
                    Prefix + "zmod_additive_group_is_prime_power_decomposable"),
                H("The additive group of positive ZMod decomposes into Sylow factors"),
                StatementSource.FromAuthor(ZModDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive modulus n, Multiplicative (ZMod n) denotes the "
                            + "multiplicative wrapper of the additive group, so its group "
                            + "operation is ring addition rather than ring multiplication.")),
                    Paragraph(Text(
                        "The group is finite and commutative, hence nilpotent. The existing "
                            + "finite prime-power quotient TFAE then supplies its exact Sylow "
                            + "direct-product decomposition without rebuilding CRT."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ne-zero-necessary-for-zmod-sylow-decomposition"),
                DeclarationHandle.Create(
                    Prefix + "ne_zero_is_necessary_for_zmod_sylow_decomposition"),
                H("The nonzero modulus hypothesis is necessary"),
                StatementSource.FromAuthor(NeZeroNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At modulus zero, ZMod is the infinite additive group of integers. Its "
                        + "natural cardinal is zero, so the Sylow prime-factor index is empty "
                        + "and its product is subsingleton, while the source is nontrivial."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("prime-primary-decomposition-does-not-lift"),
                DeclarationHandle.Create(
                    Prefix + "prime_primary_decomposition_does_not_lift"),
                H("Prime-primary decomposition does not lift unconditionally"),
                StatementSource.FromAuthor(NoncommutativeCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists a finite noncommutative group for which every map to "
                            + "every finite p-group is trivial and whose canonical prime-power "
                            + "quotient observer is therefore not injective.")),
                    Paragraph(Text(
                        "The witness is A5. The imported A5 theorem supplies uniform triviality "
                            + "of all target maps; two distinct elements then receive identical "
                            + "values in every prime-power quotient.")),
                    Paragraph(Text(
                        "This is an existential obstruction only. It does not claim that every "
                            + "noncommutative finite group lacks a prime-primary decomposition; "
                            + "noncommutative nilpotent groups are outside that false claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crt-is-a-nilpotent-abelian-victory"),
                DeclarationHandle.Create(
                    Prefix + "crt_is_a_nilpotent_abelian_victory"),
                H("The additive CRT case and its noncommutative boundary"),
                StatementSource.FromAuthor(PackagedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive n, the Sylow decomposition of additive ZMod n is paired "
                        + "with the finite A5 counterexample to an unrestricted prime-primary "
                        + "decomposition principle."))),
                DescribeRole.Theorem))));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ZModOf(Formula modulus) =>
        Seq(Operatorname, Grp(F.Id("ZMod")), Open, modulus, Close);

    private static Formula MultiplicativeOf(Formula group) =>
        Seq(Operatorname, Grp(F.Id("Multiplicative")), Open, group, Close);

    private static Formula DecomposableOf(Formula group) =>
        Seq(
            Operatorname, Grp(F.Id("SylowPrimePowerDecomposable")),
            Open, group, Close);

    private static Formula CounterexampleOf(Formula group) =>
        Seq(
            Operatorname, Grp(F.Id("PrimePrimaryDecompositionCounterexample")),
            Open, group, Close);

    private static Formula FiniteGroupOf(Formula group) =>
        Seq(Operatorname, Grp(F.Id("FiniteGroup")), Open, group, Close);

    private static Formula ObserverOf(Formula group) =>
        Seq(
            Operatorname, Grp(F.Id("primePowerQuotientObserver")),
            Open, group, Close);

    private static Formula PositiveModulus(Formula modulus) =>
        NotEqual(modulus, D(0));

    private static Formula AdditiveZMod(Formula modulus) =>
        MultiplicativeOf(ZModOf(modulus));

    private static Formula CounterexampleExistenceFormula()
    {
        Formula group = F.Id("G");
        return Seq(
            Exists, Sp, group, Comma, Sp,
            FiniteGroupOf(group), Sp, Land, Sp,
            CounterexampleOf(group));
    }

    private static Formula ZModDecompositionFormula()
    {
        Formula modulus = F.Id("n");
        return Disp(Seq(
            Forall, Sp, modulus, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            PositiveModulus(modulus), Sp, Rightarrow, Sp,
            DecomposableOf(AdditiveZMod(modulus)), Dot));
    }

    private static Formula NeZeroNecessityFormula() =>
        Disp(Seq(Neg, DecomposableOf(AdditiveZMod(D(0))), Dot));

    private static Formula NoncommutativeCounterexampleFormula()
    {
        Formula group = F.Id("G");
        Formula allTrivial = At(F.Id("AllPrimePrimaryHomomorphismsTrivial"), group);
        Formula observerNotInjective = Seq(
            Neg, Operatorname, Grp(F.Id("Injective")),
            Open, ObserverOf(group), Close);
        return Disp(Seq(
            Exists, Sp, group, Comma, Sp,
            FiniteGroupOf(group), Sp, Land, Sp,
            Operatorname, Grp(F.Id("Noncommutative")), Open, group, Close,
            Sp, Land, Sp, allTrivial, Sp, Land, Sp, observerNotInjective, Dot));
    }

    private static Formula PackagedFormula()
    {
        Formula modulus = F.Id("n");
        return Disp(Seq(
            Forall, Sp, modulus, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            PositiveModulus(modulus), Sp, Rightarrow, Sp,
            DecomposableOf(AdditiveZMod(modulus)), Sp, Land, Sp,
            CounterexampleExistenceFormula(), Dot));
    }
}
