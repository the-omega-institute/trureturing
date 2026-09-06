using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class RobinExponentSwapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/RobinExponentSwap.";
    private static readonly LibraryNoteRef AlaogluErdos =
        LibraryNoteRef.Create("D5/L/Arith/alaoglu1944highly");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assigning the larger exponent to the smaller real base strictly increases "
            + "the product of reciprocal geometric sums.",
        H("Strict Exponent Exchange"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reciprocal-geometric-sum"),
                DeclarationHandle.Create(Prefix + "reciprocalGeomSum"),
                H("Reciprocal geometric sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), Sp, InMacro, Sp, RealDomain(), Comma, Sp,
                    Forall, Sp, F.Id("k"), Sp, InMacro, Sp, NatDomain(), Comma, Sp,
                    Call("f", F.Id("r"), F.Id("k")), Sp, Eq, Sp,
                    Sum, Underscore, Grp(Seq(F.Id("i"), Eq, D(0))), Caret, Grp(F.Id("k")), Sp,
                    new Formula.Power(new Formula.Fraction(D(1), F.Id("r")), F.Id("i"))))),
                AssessedProvenance.FromLiterature(AlaogluErdos),
                Blocks(Paragraph(Text(
                    "The notation f denotes reciprocalGeomSum. Its index set includes both "
                        + "zero and k, so it contains k + 1 terms and its constant term is one. "
                        + "At a prime base this is the usual local factor in the normalized "
                        + "divisor sum. The definition uses Lean's total real inverse; the "
                        + "comparison below restricts both bases to be greater than one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strict-exponent-exchange"),
                DeclarationHandle.Create(Prefix + "reciprocal_geom_sum_swap_strict"),
                H("Larger exponents favor smaller bases"),
                StatementSource.FromAuthor(SwapFormula()),
                AssessedProvenance.FromLiterature(AlaogluErdos),
                Blocks(
                    Paragraph(Text(
                        "The statement quantifies over every pair of real bases p and q and "
                            + "every pair of natural exponents a and b, including a = 0. "
                            + "It assumes exactly 1 < p, p < q, and a < b. The right-hand "
                            + "product pairs the larger exponent with the smaller base. "
                            + "Both prefix sums are positive, so positive cross multiplication "
                            + "also gives f(q,b)/f(q,a) < f(p,b)/f(p,a).")),
                    Paragraph(Text(
                        "The proof compares every term of a fixed prefix against each "
                            + "new tail exponent. The strict ordering of the positive inverse "
                            + "bases gives a strict power comparison because every tail "
                            + "exponent exceeds every prefix exponent. Finite summation and "
                            + "induction on the larger exponent produce the displayed result.")),
                    Paragraph(Text(
                        "This is the local exchange inequality in the classical "
                            + "superabundant-number argument, stated with arbitrary real "
                            + "bases. It proves only the strict increase of the two local "
                            + "factors. The integer-size decrease, record-point construction, "
                            + "nonincreasing factorization of record points, and Robin "
                            + "criterion are not conclusions of this module."))),
                DescribeRole.Theorem))));

    private static Formula SwapFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Sp, InMacro, Sp,
            RealDomain(), Comma, Sp, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"),
            Sp, InMacro, Sp, NatDomain(), Comma),
        Seq(Open, D(1), Sp, Lt, Sp, F.Id("p"), Sp, Lt, Sp, F.Id("q"), Sp, Land,
            Sp, F.Id("a"), Sp, Lt, Sp, F.Id("b"), Close, Sp, Rightarrow),
        Seq(Product(Call("f", F.Id("p"), F.Id("a")),
                Call("f", F.Id("q"), F.Id("b"))), Sp, Lt, Sp,
            Product(Call("f", F.Id("p"), F.Id("b")),
                Call("f", F.Id("q"), F.Id("a"))), Dot)
    ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula RealDomain() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula NatDomain() => Seq(Mathbb, Grp(F.Id("N")));
}
