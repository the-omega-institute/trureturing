// UNCOMPILED research Scribe draft for CubicWilsonBinomial.lean.
// Neither this C# document nor the consumer Lean source has been compiled here.
// No emission, statement identity, report, audit, CI, or acceptance is asserted.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicWilsonBinomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/QuadraticIdeals/CubicWilsonBinomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Wilson binomial identity makes the conjugate primary generator a cube in the original residue field.",
        H("Conjugate Primary Symbols from Wilson's Identity"),
        Blocks(
            Paragraph(Text(
                "Uncompiled research draft. These author descriptions follow CubicWilsonBinomial.lean; "
                + "they have not been compiled or emitted and carry no kernel, report, audit, or acceptance claim.")),
            Paragraph(Text(
                "Fix E = Z[omega], the Eisenstein order with its standard conjugation star. For a finite maximal quotient, "
                + "chi_P denotes the actual Euler cubic residue character E/P -> E, extended by zero at zero. "
                + "Writing chi_P(a) for a in E means evaluation at a mod P. A primary generator pi satisfies "
                + "span{pi} = P and 3 divides pi-1. This consumer imports the finite-field identities from "
                + "CubicEulerWilson and the existing Jacobi normalization; it does not reprove those identities.")),
            Describe.Lean(
                DescribeId.Create("cubic-wilson-conjugate-factorial-cube"),
                DeclarationHandle.Create(Prefix + "primary_conjugate_reduction_eq_factorial_cube"),
                H("The conjugate generator reduces to an explicit factorial cube"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    PrimeResidueParameters(), PrimaryGenerator(), Sp, Implies, Sp,
                    Call("modIdeal", Call("star", F.Id("pi")), F.Id("P")), Eq,
                    Call("pow", Call("neg", Call("inv", Cast(Call("factorial", Index()), Quotient("P")))), D(3))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The hypotheses are exactly: P is maximal, E/P is finite of cardinality the rational prime p, "
                    + "p is congruent to 1 modulo 3, and pi is a specified primary generator of P. Put m = (p-1)/3. "
                    + "The existing normalization gives pi = -J(chi_P,chi_P). In this same quotient E/P, conjugating "
                    + "J replaces each character by its inverse, which is its square. Euler reduction therefore gives "
                    + "the sum of x^(2m)(1-x)^(2m). Only exponent 3m = p-1 survives its binomial expansion; m is even, "
                    + "so the value is -binomial(2m,m). The imported Wilson identity makes that value (m!^(-1))^3. "
                    + "The minus sign in pi = -J yields the displayed cube (-m!^(-1))^3. No isomorphism between "
                    + "conjugate residue fields, and no transport of their characters, occurs. Prime cardinality p "
                    + "is an explicit premise here; characteristic p alone is insufficient to apply this endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cubic-wilson-conjugate-symbol-pair"),
                DeclarationHandle.Create(Prefix + "conjugate_primary_symbol_pair"),
                H("Both conjugate-primary symbols equal one"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    PrimeResidueParameters(),
                    Forall, Sp, F.Id("Q"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
                    Call("maximal", F.Id("Q")), Comma, Sp, Call("finite", Quotient("Q")), Comma, Sp,
                    Call("card", Quotient("Q")), Eq, F.Id("p"), Comma, Sp,
                    PrimaryGenerator(), Comma, Sp,
                    Call("spanSingleton", Call("star", F.Id("pi"))), Eq, F.Id("Q"), Sp, Implies, Sp,
                    Chi("P", Call("star", F.Id("pi"))), Eq, D(1), Sp, Land, Sp,
                    Chi("Q", F.Id("pi")), Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here Q is also maximal with finite quotient of cardinality the same prime p, and Q = span{star(pi)}. "
                    + "These cardinalities are both hypotheses; their equality is not obtained from an unstated quotient "
                    + "identification. Since m < p, the factorial in the cube witness is nonzero. Fermat's theorem and "
                    + "Euler reduction give chi_P(star(pi)) = 1 after using injectivity on the three actual cubic roots. "
                    + "Conjugation preserves the primary congruence, so applying this same theorem independently in E/Q "
                    + "gives chi_Q(pi) = 1. Neither a cube witness, nonvanishing of the input, a Jacobi value, nor a "
                    + "symbol equality is supplied as an endpoint hypothesis. The later same-characteristic module "
                    + "derives the prime-cardinality data needed to consume this pair."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Cast(Formula value, Formula target) => Call("cast", value, target);
    private static Formula Quotient(string ideal) => Call("quotient", F.Id("E"), F.Id(ideal));
    private static Formula Chi(string ideal, Formula value) =>
        Call("chi", F.Id(ideal), Call("modIdeal", value, F.Id(ideal)));
    private static Formula Index() => Call("natDiv", F.Seq(F.Id("p"), Minus, D(1)), D(3));
    private static Formula PrimaryGenerator() => F.Seq(
        Forall, Sp, F.Id("pi"), Colon, Sp, F.Id("E"), Comma, Sp,
        Call("spanSingleton", F.Id("pi")), Eq, F.Id("P"), Comma, Sp,
        Call("divides", Cast(D(3), F.Id("E")), F.Seq(F.Id("pi"), Minus, D(1))));
    private static Formula PrimeResidueParameters() => F.Seq(
        Forall, Sp, F.Id("P"), Colon, Sp, Call("Ideal", F.Id("E")), Comma, Sp,
        Call("maximal", F.Id("P")), Comma, Sp, Call("finite", Quotient("P")), Comma, Sp,
        Forall, Sp, F.Id("p"), Colon, Sp, F.Id("Nat"), Comma, Sp,
        Call("prime", F.Id("p")), Comma, Sp, Call("card", Quotient("P")), Eq, F.Id("p"), Comma, Sp,
        Call("mod", F.Id("p"), D(3)), Eq, D(1), Comma, Sp);
}
