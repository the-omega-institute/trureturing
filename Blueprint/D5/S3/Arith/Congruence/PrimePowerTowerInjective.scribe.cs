using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PrimePowerTowerInjectiveDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Arith/Congruence/PrimePowerTowerInjective.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive prime-power reductions separate integers, and equality of their complete "
            + "reduction towers is exactly integer equality.",
        H("Integer Separation by the Prime-Power Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-prime-power-tower-is-injective"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "precision_tower_injective"),
                H("Positive prime-power reductions determine an integer"),
                StatementSource.FromAuthor(InjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a prime p. The precision tower sends an integer x to the family "
                            + "whose coordinate k is the residue of x modulo p^(k + 1). The "
                            + "shift starts the tower at the first positive precision p^1 and "
                            + "omits the trivial exponent-zero quotient.")),
                    Paragraph(Text(
                        "If two distinct integers had the same tower, let v be the p-adic "
                            + "valuation of their difference. Equality of coordinate v would "
                            + "make their precision-(v + 1) readings equal, while the preceding "
                            + "least-distinguishing-precision theorem says that this is exactly "
                            + "a precision where they differ. Thus every tower collision is an "
                            + "integer equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tower-equality-is-integer-equality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "precision_tower_eq_iff"),
                H("Tower equality is exactly integer equality"),
                StatementSource.FromAuthor(EqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed prime, two integers have identical families of reductions "
                            + "modulo every positive power of that prime exactly when the integers "
                            + "themselves are equal.")),
                    Paragraph(Text(
                        "The forward direction is the injectivity of the complete precision "
                            + "tower. The reverse direction follows because equal integers have "
                            + "equal reductions in every coordinate."))),
                DescribeRole.Proposition))));

    private static Formula Tower(Formula prime, Formula value) =>
        Call("precisionTower", prime, value);

    private static Formula InjectivityFormula()
    {
        Formula prime = F.Id("p");
        Formula index = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula modulus = Seq(
            prime, Caret, Grp(index, Sp, Plus, Sp, D(1)));
        Formula codomain = Seq(
            Prod, Underscore, Grp(index, Sp, InMacro, Sp, naturals), Sp,
            Call("ZMod", modulus));
        Formula towerMap = Seq(
            Call("precisionTower", prime), Sp, Colon, Sp,
            integers, Sp, To, Sp, codomain);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Sp, InMacro, Sp, naturals, Comma, RowBreak, Grp(),
            Call("Prime", prime), Sp, Rightarrow, Sp,
            Call("Injective", towerMap), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula EqualityFormula()
    {
        Formula prime = F.Id("p");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Sp, InMacro, Sp, naturals, Comma, RowBreak, Grp(),
            left, Comma, Sp, right, Sp, InMacro, Sp, integers, Comma, RowBreak, Grp(),
            Call("Prime", prime), Sp, Rightarrow, Sp, Open,
            Tower(prime, left), Sp, Eq, Sp, Tower(prime, right),
            Sp, Iff, Sp, left, Sp, Eq, Sp, right, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
