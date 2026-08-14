using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeAddress;

internal sealed class PrimeLogIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique factorization makes the logarithms of the primes linearly independent over the rationals.",
        H("Rational Independence of Prime Logarithms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-logarithms-are-integer-linearly-independent"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeAddress/PrimeLogIndependence.prime_log_integer_independence"),
                H("Prime logarithms are integer-linearly independent"),
                StatementSource.FromAuthor(IntegerLinearIndependenceStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The family p maps to log p, indexed by the natural primes and valued in the "
                    + "reals, is linearly independent over the integers. This declaration adapts the "
                    + "repository's existing finite-relation theorem prime_log_indep to Mathlib's "
                    + "LinearIndependent interface; the existing theorem supplies the unique-"
                    + "factorization argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-logarithms-are-rationally-linearly-independent"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeAddress/PrimeLogIndependence.prime_log_rational_independence"),
                H("Prime logarithms are rationally linearly independent"),
                StatementSource.FromAuthor(RationalLinearIndependenceStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same prime-indexed real family is linearly independent over the rationals. "
                    + "Mathlib's fraction-ring equivalence reduces this assertion to the preceding "
                    + "integer theorem, thereby proving the denominator-clearing step rather than "
                    + "assuming it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-rational-log-two-log-three-relation-is-trivial"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeAddress/PrimeLogIndependence.log_two_log_three_relation_eq_zero"),
                H("Every rational relation between log two and log three is trivial"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("Q")), Comma, Esc,
                    F.Id("a"), Sp, Cdot, Sp, Log, Sp, D(2), Sp, Plus, Sp,
                    F.Id("b"), Sp, Cdot, Sp, Log, Sp, D(3), Sp, Eq, Sp, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("a"), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    F.Id("b"), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For rational coefficients a and b, a log 2 plus b log 3 can vanish only when "
                    + "both coefficients vanish. This is the two-coordinate specialization of the "
                    + "prime-family theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-one-minus-one-log-two-log-three-relation-does-not-vanish"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeAddress/PrimeLogIndependence.log_two_sub_log_three_ne_zero"),
                H("The coefficient pair one and minus one gives no vanishing relation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Sp, Colon, Sp, Mathbb, Grp(F.Id("Q")), Close,
                    Sp, Cdot, Sp, Log, Sp, D(2), Sp, Plus, Sp,
                    Open, Minus, D(1), Sp, Colon, Sp, Mathbb, Grp(F.Id("Q")), Close,
                    Sp, Cdot, Sp, Log, Sp, D(3), Sp, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit nontrivial rational coefficient pair (1, -1) does not annihilate "
                    + "log 2 and log 3. This checked instance prevents the general independence "
                    + "statement from being vacuous."))),
                DescribeRole.Theorem)),
        []));

    private static Formula IntegerLinearIndependenceStatement() => Disp(Seq(
        Operatorname, Grp(F.Id("LinearIndependent")), Underscore,
        Grp(Mathbb, Grp(F.Id("Z"))),
        Open,
        F.Id("p"), Sp, Mapsto, Sp, Log, Sp, F.Id("p"),
        Sp, Colon, Sp,
        Operatorname, Grp(F.Id("Primes")), Sp, To, Sp, Mathbb, Grp(F.Id("R")),
        Close));

    private static Formula RationalLinearIndependenceStatement() => Disp(Seq(
        Operatorname, Grp(F.Id("LinearIndependent")), Underscore,
        Grp(Mathbb, Grp(F.Id("Q"))),
        Open,
        F.Id("p"), Sp, Mapsto, Sp, Log, Sp, F.Id("p"),
        Sp, Colon, Sp,
        Operatorname, Grp(F.Id("Primes")), Sp, To, Sp, Mathbb, Grp(F.Id("R")),
        Close));
}
