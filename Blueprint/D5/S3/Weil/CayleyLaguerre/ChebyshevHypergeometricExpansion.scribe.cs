using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class ChebyshevHypergeometricExpansionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/CayleyLaguerre/ChebyshevHypergeometricExpansion."
            + "shifted_chebyshev_hypergeometric_expansion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shifted first-kind Chebyshev polynomial has its terminating "
            + "hypergeometric expansion.",
        H("Shifted Chebyshev Hypergeometric Expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("shifted-chebyshev-hypergeometric-expansion"),
            DeclarationHandle.Create(Declaration),
            H("Shifted Chebyshev polynomials have explicit Pochhammer coefficients"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural degree, evaluating the first-kind Chebyshev "
                        + "polynomial at one minus twice the real input gives the displayed "
                        + "finite sum of rising-Pochhammer coefficients.")),
                Paragraph(Text(
                    "This formalizes the self-contained identities (541.4)-(541.5). The "
                        + "earlier analytic notation in the source is not used: R_a is "
                        + "undefined there, and (541.1) reuses nu where later formulas "
                        + "require both a measure nu and a square-scale variable u.")),
                Paragraph(Text(
                    "The proof combines polynomial Taylor expansion with Mathlib's "
                        + "recurrence for iterated derivatives of Chebyshev polynomials at "
                        + "one and the rising-Pochhammer successor identity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula k = F.Id("k");
        Formula shifted = Call("ChebyshevT", n, Subtract(D(1), Multiply(D(2), x)));
        Formula coefficient = new Formula.Fraction(
            Multiply(
                Pochhammer(new Formula.Negate(n), k),
                Pochhammer(n, k)),
            Multiply(
                Pochhammer(new Formula.Fraction(D(1), D(2)), k),
                Call("factorial", k)));
        Formula expansion = Seq(
            Sum, Underscore, Grp(k, Sp, Eq, Sp, D(0)), Caret, Grp(n), Sp,
            Multiply(coefficient, Power(x, k)));

        return Disp(ForAll(
            [Bound("n", natural), Bound("x", real)],
            Equal(shifted, expansion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pochhammer(Formula value, Formula index) =>
        Call("risingPochhammer", value, index);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, Seq(exponent));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
