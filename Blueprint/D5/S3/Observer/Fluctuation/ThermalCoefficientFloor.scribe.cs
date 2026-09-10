using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Fluctuation;

internal sealed class ThermalCoefficientFloorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Fluctuation/ThermalCoefficientFloor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The thermal response coefficient is bounded below by the inverse temperature, "
        + "with no common floor on the mode frequencies.",
        H("Thermal Coefficient Floor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hyperbolic-sine-monotonicity-estimate"),
                DeclarationHandle.Create(Prefix + "sinh_le_self_mul_cosh_of_nonneg"),
                H("A hyperbolic estimate"),
                StatementSource.FromAuthor(SinhStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The difference between the two sides vanishes at the origin and has "
                    + "derivative equal to the argument times the hyperbolic sine, which is "
                    + "nonnegative on the nonnegative axis. Monotonicity from a nonnegative "
                    + "derivative then gives the estimate. The pinned library carries the "
                    + "derivatives and the sign of the hyperbolic sine, but no inequality of "
                    + "this shape."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hyperbolic-cotangent"),
                DeclarationHandle.Create(Prefix + "coth"),
                H("The hyperbolic cotangent"),
                StatementSource.FromAuthor(CothStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient is taken in the real numbers, so it is totalized at the "
                    + "origin. Every statement below assumes a positive argument, where the "
                    + "denominator is positive and the quotient is the intended one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("argument-times-cotangent-at-least-one"),
                DeclarationHandle.Create(Prefix + "one_le_self_mul_coth"),
                H("Companion: the product is at least one"),
                StatementSource.FromAuthor(ProductStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Clearing the positive denominator turns the claim into the estimate "
                    + "above."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("cotangent-dominates-reciprocal"),
                DeclarationHandle.Create(Prefix + "inv_le_coth"),
                H("Companion: the cotangent dominates the reciprocal"),
                StatementSource.FromAuthor(ReciprocalStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same inequality divided by the positive argument. This is the form "
                    + "the coefficient bound consumes."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("inverse-temperature-floor"),
                DeclarationHandle.Create(Prefix + "inv_le_thermal_coefficient"),
                H("The coefficient floor"),
                StatementSource.FromAuthor(CoefficientStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The right-hand side is the inverse temperature alone. Its proof uses "
                    + "only that this one frequency is positive; no quantity shared across "
                    + "frequencies enters. The two positive constants cancel exactly, which "
                    + "is why nothing about their size survives into the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-spectral-floor"),
                DeclarationHandle.Create(Prefix + "inv_mul_sum_le_thermal_sum"),
                H("The finite spectral form"),
                StatementSource.FromAuthor(SumStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each mode carries its own positive frequency and a nonnegative weight, "
                    + "so the pointwise bound applies term by term over a finite index type. "
                    + "No summability hypothesis is needed and none is claimed; extending to "
                    + "a countable index would require convergence of both sides and is not "
                    + "addressed here."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The source states this bound together with a second one under a single "
                + "hypothesis: a common positive floor below every frequency. Only the "
                + "second bound uses that floor, and its coefficient displays it. The first "
                + "bound, isolated here, holds under the weaker hypothesis that each "
                + "frequency is positive in its own right.")),
            Paragraph(Text(
                "Nothing here identifies the sum with a physical fluctuation. That "
                + "identification is an equilibrium preparation statement and is a separate "
                + "hypothesis; no canonical quantization, state preparation, or measurement "
                + "rule is formalized in this module.")))));

    private static Formula SinhStatement() =>
        ForReals(["x"], Seq(D(0), Sp, Leq, Sp, X(), Sp, Rightarrow, Sp,
            Sinh(X()), Sp, Leq, Sp, Mul(X(), Cosh(X()))));

    private static Formula CothStatement() =>
        ForReals(["x"], Equal(Coth(X()), Divide(Cosh(X()), Sinh(X()))));

    private static Formula ProductStatement() =>
        ForReals(["x"], Seq(D(0), Sp, Lt, Sp, X(), Sp, Rightarrow, Sp,
            D(1), Sp, Leq, Sp, Mul(X(), Coth(X()))));

    private static Formula ReciprocalStatement() =>
        ForReals(["x"], Seq(D(0), Sp, Lt, Sp, X(), Sp, Rightarrow, Sp,
            Divide(D(1), X()), Sp, Leq, Sp, Coth(X())));

    private static Formula CoefficientStatement()
    {
        Formula beta = F.Id("beta"), hbar = F.Id("hbar"), nu = F.Id("nu");
        Formula arg = Divide(Seq(beta, Sp, Cdot, Sp, hbar, Sp, Cdot, Sp, nu), D(2));
        return ForReals(["beta", "hbar", "nu"],
            Seq(Positive(beta), Sp, Land, Sp, Positive(hbar), Sp, Land, Sp, Positive(nu),
                Sp, Rightarrow, Sp,
                Divide(D(1), beta), Sp, Leq, Sp,
                Mul(Divide(Seq(hbar, Sp, Cdot, Sp, nu), D(2)), Coth(arg))));
    }

    private static Formula SumStatement()
    {
        Formula beta = F.Id("beta"), hbar = F.Id("hbar");
        Formula nu = Call("nu", F.Id("a")), w = Call("w", F.Id("a"));
        Formula weight = Divide(w, Square(nu));
        Formula arg = Divide(Seq(beta, Sp, Cdot, Sp, hbar, Sp, Cdot, Sp, nu), D(2));
        Formula coeff = Mul(Divide(Seq(hbar, Sp, Cdot, Sp, nu), D(2)), Coth(arg));
        Formula sumL = Seq(new Formula.Subscript(F.Sum, F.Id("a")), Sp, weight);
        Formula sumR = Seq(new Formula.Subscript(F.Sum, F.Id("a")), Sp, Mul(coeff, weight));
        return Disp(Seq(Forall, Sp, F.Id("a"), Comma, Sp,
            Positive(nu), Sp, Land, Sp, D(0), Sp, Leq, Sp, w, Sp, Rightarrow, Sp,
            Mul(Divide(D(1), beta), sumL), Sp, Leq, Sp, sumR));
    }

    private static Formula X() => F.Id("x");
    private static Formula Positive(Formula v) => Seq(D(0), Sp, Lt, Sp, v);
    private static Formula Sinh(Formula v) => Call("sinh", v);
    private static Formula Cosh(Formula v) => Call("cosh", v);
    private static Formula Coth(Formula v) => Call("coth", v);

    private static Formula ForReals(string[] names, Formula body) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("R")))))], body));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Square(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));
    private static Formula Divide(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
}
