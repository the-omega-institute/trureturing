using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeAddress;

internal sealed class PrimePowerDiffractionAtomDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit-formula summand at a positive prime power has its exact logarithmic "
            + "location and midline weight.",
        H("Prime-Power Diffraction Atom"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-diffraction-atom"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeAddress/PrimePowerDiffractionAtom."
                        + "prime_power_diffraction_atom"),
                H("A prime-power summand has the canonical location and weight"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p and a nonzero natural exponent m, the sampled address "
                            + "log(p^m) is m log p. The von Mangoldt coefficient and real-power "
                            + "factor jointly reduce to log p times p^(-m/2).")),
                    Paragraph(Text(
                        "Substituting both identities into the repository's primeSummand gives "
                            + "the full normalized explicit-formula atom, including its two "
                            + "symmetric test-function evaluations.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies vonMangoldt_apply_pow, "
                            + "vonMangoldt_apply_prime, log_pow, rpow_mul, and rpow_natCast. "
                            + "The theorem does not assert an RH equivalence or a quasicrystal "
                            + "interpretation, for which the source provides no formal carrier."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pow(Formula basis, Formula exponent) =>
        Seq(basis, Caret, Grp(exponent));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p");
        Formula m = F.Id("m");
        Formula g = F.Id("g");
        Formula pm = Pow(p, m);
        Formula logP = Apply(Seq(Operatorname, Grp(F.Id("log"))), p);
        Formula location = Seq(
            Apply(Seq(Operatorname, Grp(F.Id("log"))), pm), Sp, Eq, Sp,
            m, Sp, Cdot, Sp, logP);
        Formula exponent = Seq(Minus, m, Slash, D(2));
        Formula weight = Seq(
            Apply(Lambda, pm), Sp, Cdot, Sp,
            Pow(Grp(pm), Seq(Minus, D(1), Slash, D(2))),
            Sp, Eq, Sp, logP, Sp, Cdot, Sp, Pow(p, exponent));
        Formula sample = Seq(
            Call("primeSummand", g, pm),
            Sp, Eq, Sp, logP, Sp, Cdot, Sp, Pow(p, exponent), Sp, Cdot, Sp,
            Open, Apply(g, Seq(m, Sp, Cdot, Sp, logP)), Sp, Plus, Sp,
            Apply(g, Seq(Minus, Open, m, Sp, Cdot, Sp, logP, Close)), Close);

        return Disp(Seq(
            Forall, Sp, g, Comma, Sp, p, Comma, Sp, m, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp,
            Operatorname, Grp(F.Id("Prime")), Open, p, Close,
            Sp, Land, Sp, m, Sp, Neq, Sp, D(0), Sp, Rightarrow, RowBreak,
            location, Sp, Land, RowBreak, weight, Sp, Land, RowBreak, sample, Dot));
    }
}
