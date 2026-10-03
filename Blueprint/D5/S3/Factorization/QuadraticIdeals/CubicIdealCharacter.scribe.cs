using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicIdealCharacterDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/QuadraticIdeals/CubicIdealCharacter."
        + "cubic_ideal_character_and_factored_multiplicativity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local cubic character is selected by the prime-ideal Euler criterion, "
            + "and factored denominators preserve both multiplication laws.",
        H("Cubic Characters on Factored Eisenstein Ideals"),
        Blocks(Describe.Lean(
            DescribeId.Create("eisenstein-prime-ideal-cubic-character"),
            DeclarationHandle.Create(Declaration),
            H("Local uniqueness and composite-denominator multiplication"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let E be the Eisenstein order, omega its distinguished cube root of "
                        + "unity, and S a finite index set. Each P_i is maximal, E/P_i is "
                        + "finite of order q_i congruent to one modulo three, and 3 is not "
                        + "in P_i; write Admissible(S,P) for these conditions at every "
                        + "i in S. The exponent m_i is (q_i - 1)/3. The condition C_S(a) "
                        + "means that a lies in none of the P_i.")),
                Paragraph(Text(
                    "The function chi at P_i returns one of 1, omega, omega squared. "
                        + "For a outside P_i, its residue is the m_i-th power of a, and "
                        + "no other member of those three roots has that residue. The "
                        + "three classes are distinct because any coincidence would put "
                        + "3 in P_i. Fermat's theorem and the factorization of T cubed "
                        + "minus one establish existence.")),
                Paragraph(Text(
                    "The character of a specified factored denominator is the product "
                        + "of the local characters raised to their ideal multiplicities. "
                        + "It multiplies in the numerator, and adding multiplicities "
                        + "multiplies the denominator characters. The definition never "
                        + "uses one Euler exponent in a composite quotient."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("S");
        Formula p = F.Id("P");
        Formula i = F.Id("i");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula z = F.Id("z");
        Formula e = F.Id("e");
        Formula f = F.Id("f");
        Formula pi = new Formula.Subscript(p, i);
        Formula qi = new Formula.Subscript(F.Id("q"), i);
        Formula mi = new Formula.Subscript(F.Id("m"), i);
        Formula roots = new Formula.Subscript(Mu, D(3));
        Formula chiA = Call("chi", pi, a);
        Formula chiB = Call("chi", pi, b);
        Formula chiAB = Call("chi", pi, Seq(a, Sp, Cdot, Sp, b));
        Formula residueA = new Formula.Subscript(Seq(OpenBracket, a, CloseBracket), pi);
        Formula residueZ = new Formula.Subscript(Seq(OpenBracket, z, CloseBracket), pi);
        Formula residueChi = new Formula.Subscript(Seq(OpenBracket, chiA, CloseBracket), pi);
        Formula eplusf = Seq(e, Sp, Plus, Sp, f);
        Formula admissible = Call("Admissible", s, p);
        Formula coprimeA = Call("C", s, a);
        Formula coprimeB = Call("C", s, b);
        Formula product = Seq(new Formula.Subscript(Prod,
                Seq(i, Sp, InMacro, Sp, s)), Sp,
            new Formula.Power(chiA, new Formula.Subscript(e, i)));

        return Disp(new Formula.Aligned([
            Seq(admissible, Sp, Rightarrow, Sp,
                Forall, Sp, i, Sp, InMacro, Sp, s, Comma, Sp,
                qi, Sp, Eq, Sp, Call("card", Call("Quotient", F.Id("E"), pi)),
                Sp, Land, Sp,
                mi, Sp, Eq, Sp,
                new Formula.Fraction(Seq(qi, Sp, Minus, Sp, D(1)), D(3))),
            Seq(admissible, Sp, Rightarrow, Sp,
                Forall, Sp, i, Sp, InMacro, Sp, s, Comma, Sp,
                Forall, Sp, a, Comma, Sp,
                Neg, Sp, Open, a, Sp, InMacro, Sp, pi, Close,
                Sp, Rightarrow, Sp,
                chiA, Sp, InMacro, Sp, roots, Sp, Land, Sp,
                residueChi, Sp, Eq, Sp, new Formula.Power(residueA, mi)),
            Seq(admissible, Sp, Rightarrow, Sp,
                Forall, Sp, i, Sp, InMacro, Sp, s, Comma, Sp,
                Forall, Sp, a, Comma, Sp,
                Neg, Sp, Open, a, Sp, InMacro, Sp, pi, Close,
                Sp, Rightarrow, Sp,
                Forall, Sp, z, Sp, InMacro, Sp, roots, Comma, Sp,
                residueZ, Sp, Eq, Sp, new Formula.Power(residueA, mi),
                Sp, Rightarrow, Sp, z, Sp, Eq, Sp, chiA),
            Seq(admissible, Sp, Rightarrow, Sp,
                Forall, Sp, i, Sp, InMacro, Sp, s, Comma, Sp,
                Forall, Sp, a, Comma, b, Comma, Sp,
                Neg, Sp, Open, a, Sp, InMacro, Sp, pi, Close, Sp, Land, Sp,
                Neg, Sp, Open, b, Sp, InMacro, Sp, pi, Close,
                Sp, Rightarrow, Sp, chiAB, Sp, Eq, Sp,
                chiA, Sp, Cdot, Sp, chiB),
            Seq(Call("Chi", s, p, e, a), Sp, Eq, Sp, product),
            Seq(admissible, Sp, Rightarrow, Sp,
                Forall, Sp, e, Comma, a, Comma, b, Comma, Sp,
                coprimeA, Sp, Land, Sp, coprimeB, Sp, Rightarrow, Sp,
                Call("Chi", s, p, e, Seq(a, Sp, Cdot, Sp, b)), Sp, Eq, Sp,
                Call("Chi", s, p, e, a), Sp, Cdot, Sp,
                Call("Chi", s, p, e, b)),
            Seq(admissible, Sp, Rightarrow, Sp,
                Forall, Sp, e, Comma, f, Comma, a, Comma, Sp,
                coprimeA, Sp, Rightarrow, Sp,
                Call("Chi", s, p, eplusf, a), Sp, Eq, Sp,
                Call("Chi", s, p, e, a), Sp, Cdot, Sp,
                Call("Chi", s, p, f, a)),
        ]));
    }
}
