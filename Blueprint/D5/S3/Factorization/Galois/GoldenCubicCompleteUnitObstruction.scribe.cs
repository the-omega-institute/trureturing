using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GoldenCubicCompleteUnitObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The primary and conjugate factors of earlier golden cubic blocks, together with two and three, generate a full-degree Galois cubic radical field in which the cubic root of unity remains noncube.",
        H("Complete Earlier Support and the Cubic Unit"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-complete-degree-and-unit-obstruction"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/Galois/GoldenCubicCompleteUnitObstruction.golden_cubic_complete_degree_and_unit_obstruction"),
            H("Full Galois degree, cubic coordinates and unit obstruction"),
            StatementSource.FromAuthor(ConclusionFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let j be a natural number and E the cubic cyclotomic field over the rationals. "
                        + "In an algebraic closure of E, collect the rational primes in blocks "
                        + "B_i = L_(3^i)^2 + 3 for indices one less than or equal to i less than j. "
                        + "Call this finite union S_j. There is one choice of primary Eisenstein "
                        + "factors pi_p for the whole union, with prime principal ideal, norm p, "
                        + "pi_p congruent to one modulo three, and p congruent to one modulo three. "
                        + "Each factor is coprime to its conjugate, and distinct rational primes "
                        + "give coprime factors in all four primary and conjugate combinations.")),
                Paragraph(Text(
                    "This same choice gives the oriented product of every earlier block. "
                        + "The exponent at p is its original Fibonacci depth, the p-adic "
                        + "valuation of F_(rho(p)), where rho(p) is the entry rank. "
                        + "Choose cube roots of each primary factor and each conjugate factor "
                        + "and of two and three. Let M_j be their common generated field over E. "
                        + "Its degree is three to the power two times the cardinality of S_j "
                        + "plus two, and no element of M_j cubes to the chosen primitive "
                        + "cube root of unity in E. The field is Galois over E. Its automorphisms "
                        + "are independent rotations of these chosen cubic roots, with one "
                        + "coordinate modulo three for each root. The support is empty for j "
                        + "at most one; the two rational radicands are still present.")),
                Paragraph(Text(
                    "Principal prime-ideal valuations distinguish the primary and conjugate "
                        + "radicands. The valuations above two and three distinguish the "
                        + "remaining radicands. Each diagonal integer valuation is nonzero "
                        + "modulo three, every off-diagonal valuation is zero, and all rows "
                        + "vanish on the cubic unit. A cube equation in the unit times the "
                        + "radicand span forces every radicand exponent to be divisible by "
                        + "three. Removing their cubes would make the unit a cube in E, "
                        + "which would put a primitive ninth root of unity in E. "
                        + "Saturated base-field tests and cubic descent propagate this "
                        + "obstruction through the entire tower while proving each stage "
                        + "has degree three."))),
            DescribeRole.Theorem))));

    private static Formula ConclusionFormula()
    {
        Formula j = F.Id("j");
        Formula support = new Formula.Subscript(F.Id("S"), j);
        Formula field = new Formula.Subscript(F.Id("M"), j);
        Formula baseField = F.Id("E");
        Formula x = F.Id("x");
        Formula cardinality = Seq(Vert, Sp, support, Sp, Vert);
        Formula exponent = Seq(D(2), cardinality, Plus, D(2));
        Formula zeta = new Formula.Subscript(F.Id("zeta"), D(3));
        return Disp(new Formula.Aligned([
            Seq(OpenBracket, field, Colon, baseField, CloseBracket,
                Sp, Eq, Sp, new Formula.Power(D(3), exponent), Comma),
            Seq(Forall, Sp, x, Sp, InMacro, Sp, field, Comma, Sp,
                new Formula.Power(x, D(3)), Sp, Neq, Sp, zeta, Comma),
            Seq(Call("Gal", field, baseField), Sp, Sim, Sp,
                new Formula.Power(new Formula.Subscript(F.Id("C"), D(3)), exponent), Dot),
        ]));
    }
}
