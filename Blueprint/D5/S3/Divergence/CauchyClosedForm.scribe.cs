using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class CauchyClosedFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The displayed Cauchy KL closed form is symmetric, nonnegative, rigid at zero, "
            + "and reduces to the scalar horizon free energy for shifted scales.",
        H("Cauchy KL Closed Form and Horizon Free Energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cauchy-kl-closed-form"),
                Handle("cauchyKL"),
                H("Cauchy KL closed form"),
                StatementSource.FromAuthor(CauchyDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For centers gamma-one and gamma-two and real scales delta-one "
                            + "and delta-two, cauchyKL is defined as the logarithm of the "
                            + "displayed rational expression. The divergence theorems below "
                            + "assume both scales are positive.")),
                    Paragraph(Text(
                        "Mathlib provides cauchyMeasure and the measure-valued klDiv API, "
                            + "but the pinned library has no theorem evaluating klDiv between "
                            + "two non-identical Cauchy measures and no integral theorem for "
                            + "the required shifted logarithmic quadratic. Accordingly this is "
                            + "the atom's closed form as a real-valued definition, not a claim "
                            + "that the missing measure integral has been evaluated."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("scalar-horizon-free-energy"),
                Handle("horizonFreeEnergy"),
                H("Scalar horizon free energy"),
                StatementSource.FromAuthor(HorizonDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a scalar singular-value ratio sigma, the horizon expression is "
                        + "minus log of one minus sigma squared. This definition records the "
                        + "rank-one scalar specialization; it does not introduce a Hankel "
                        + "operator or formalize the determinant in formula (1398.5)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cauchy-kl-closed-form-is-symmetric"),
                Handle("cauchy_kl_divergence_symm"),
                H("The Cauchy KL closed form is symmetric"),
                StatementSource.FromAuthor(SymmetryStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Swapping the two laws preserves the squared scale sum, changes the "
                        + "location difference only by a sign before squaring, and merely "
                        + "reorders the two scale factors in the denominator. Hence this "
                        + "one-dimensional Cauchy closed form is symmetric, unlike KL "
                        + "divergence in general."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cauchy-kl-logarithm-argument-at-least-one"),
                Handle("one_le_cauchy_kl_argument"),
                H("The logarithm argument is at least one"),
                StatementSource.FromAuthor(ArgumentBoundStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive scales the denominator is positive. After clearing it, "
                        + "the desired inequality is exactly the nonnegativity of the sum "
                        + "of the squared scale difference and squared center difference."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("cauchy-kl-closed-form-is-nonnegative"),
                Handle("cauchy_kl_divergence_nonneg"),
                H("The Cauchy KL closed form is nonnegative"),
                StatementSource.FromAuthor(NonnegativeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The preceding lower bound places the logarithm argument at least at "
                        + "one, so monotonicity of the real logarithm gives nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-cauchy-kl-characterizes-equal-parameters"),
                Handle("cauchy_kl_divergence_eq_zero_iff"),
                H("Zero Cauchy KL characterizes equal parameters"),
                StatementSource.FromAuthor(ZeroStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The argument bound rules out the zero and minus-one branches of the "
                        + "real-logarithm zero theorem. The remaining equality at one reduces "
                        + "to a sum of two nonnegative squares being zero, forcing equality "
                        + "of both centers and both positive scales. The converse evaluates "
                        + "the logarithm at one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shifted-cauchy-kl-equals-horizon-free-energy"),
                Handle("shifted_cauchy_kl_eq_horizon_free_energy"),
                H("Shifted Cauchy KL equals the scalar horizon free energy"),
                StatementSource.FromAuthor(ShiftedStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For zero-less-than omega-less-than delta, the shifted scales "
                            + "delta minus omega and delta plus omega are both positive. "
                            + "Substitution into the equal-center Cauchy formula reduces its "
                            + "argument to the inverse of one minus (omega/delta) squared.")),
                    Paragraph(Text(
                        "Taking the logarithm of that inverse yields minus log of one minus "
                            + "the squared ratio, exactly the scalar horizon free energy. "
                            + "This formalizes formulas (1398.2)--(1398.4). The source atom "
                            + "ends after displaying the separate operator determinant formula "
                            + "(1398.5), so no absent operator-level bridge is asserted."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create("D5/S3/Divergence/CauchyClosedForm." + declaration);

    private static Formula CauchyDefinition()
    {
        var gamma1 = Subscript("gamma", 1);
        var delta1 = Subscript("delta", 1);
        var gamma2 = Subscript("gamma", 2);
        var delta2 = Subscript("delta", 2);
        return FourReals(gamma1, delta1, gamma2, delta2, Seq(
            CauchyKl(gamma1, delta1, gamma2, delta2), Sp, Eq, Sp,
            Log(CauchyArgument(gamma1, delta1, gamma2, delta2)), Dot));
    }

    private static Formula HorizonDefinition()
    {
        var sigma = F.Id("sigma");
        return Disp(Seq(
            Forall, Sp, sigma, Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            Horizon(sigma), Sp, Eq, Sp, Minus,
            Log(Subtract(D(1), Square(sigma))), Dot));
    }

    private static Formula SymmetryStatement()
    {
        var gamma1 = Subscript("gamma", 1);
        var delta1 = Subscript("delta", 1);
        var gamma2 = Subscript("gamma", 2);
        var delta2 = Subscript("delta", 2);
        return FourReals(gamma1, delta1, gamma2, delta2, Seq(
            CauchyKl(gamma1, delta1, gamma2, delta2), Sp, Eq, Sp,
            CauchyKl(gamma2, delta2, gamma1, delta1), Dot));
    }

    private static Formula ArgumentBoundStatement()
    {
        var gamma1 = Subscript("gamma", 1);
        var delta1 = Subscript("delta", 1);
        var gamma2 = Subscript("gamma", 2);
        var delta2 = Subscript("delta", 2);
        return FourReals(gamma1, delta1, gamma2, delta2, Seq(
            PositiveScales(delta1, delta2), Sp, Rightarrow, Sp,
            D(1), Sp, Le, Sp, CauchyArgument(gamma1, delta1, gamma2, delta2), Dot));
    }

    private static Formula NonnegativeStatement()
    {
        var gamma1 = Subscript("gamma", 1);
        var delta1 = Subscript("delta", 1);
        var gamma2 = Subscript("gamma", 2);
        var delta2 = Subscript("delta", 2);
        return FourReals(gamma1, delta1, gamma2, delta2, Seq(
            PositiveScales(delta1, delta2), Sp, Rightarrow, Sp,
            D(0), Sp, Le, Sp, CauchyKl(gamma1, delta1, gamma2, delta2), Dot));
    }

    private static Formula ZeroStatement()
    {
        var gamma1 = Subscript("gamma", 1);
        var delta1 = Subscript("delta", 1);
        var gamma2 = Subscript("gamma", 2);
        var delta2 = Subscript("delta", 2);
        return FourReals(gamma1, delta1, gamma2, delta2, Seq(
            PositiveScales(delta1, delta2), Sp, Rightarrow, Sp,
            Open,
            Open, CauchyKl(gamma1, delta1, gamma2, delta2), Sp, Eq, Sp, D(0), Close,
            Sp, Leftrightarrow, Sp,
            Open, gamma1, Sp, Eq, Sp, gamma2, Sp, Land, Sp,
            delta1, Sp, Eq, Sp, delta2, Close, Close, Dot));
    }

    private static Formula ShiftedStatement()
    {
        var gamma = F.Id("gamma");
        var delta = F.Id("delta");
        var omega = F.Id("omega");
        return Disp(Seq(
            Forall, Sp, gamma, Comma, Sp, delta, Comma, Sp, omega,
            Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            Open, D(0), Sp, Lt, Sp, omega, Sp, Land, Sp,
            omega, Sp, Lt, Sp, delta, Close, Sp, Rightarrow, Sp,
            CauchyKl(
                gamma, Subtract(delta, omega), gamma, Add(delta, omega)),
            Sp, Eq, Sp, Horizon(new Formula.Fraction(omega, delta)), Dot));
    }

    private static Formula FourReals(
        Formula gamma1,
        Formula delta1,
        Formula gamma2,
        Formula delta2,
        Formula body) => Disp(Seq(
            Forall, Sp, gamma1, Comma, Sp, delta1, Comma, Sp,
            gamma2, Comma, Sp, delta2, Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            body));

    private static Formula CauchyKl(
        Formula gamma1,
        Formula delta1,
        Formula gamma2,
        Formula delta2) => Seq(
            F.Id("D"), Underscore, Grp(F.Id("C")), Open,
            gamma1, Comma, Sp, delta1, Sp, Vert, Sp,
            gamma2, Comma, Sp, delta2, Close);

    private static Formula CauchyArgument(
        Formula gamma1,
        Formula delta1,
        Formula gamma2,
        Formula delta2) => new Formula.Fraction(
            Add(Square(Add(delta1, delta2)), Square(Subtract(gamma1, gamma2))),
            Multiply(Multiply(D(4), delta1), delta2));

    private static Formula PositiveScales(Formula delta1, Formula delta2) => Seq(
        Open, D(0), Sp, Lt, Sp, delta1, Sp, Land, Sp,
        D(0), Sp, Lt, Sp, delta2, Close);

    private static Formula Horizon(Formula sigma) =>
        Seq(F.Id("F"), Open, sigma, Close);

    private static Formula Log(Formula value) =>
        Seq(Operatorname, Grp(F.Id("log")), Open, value, Close);

    private static Formula Subscript(string name, int index) =>
        new Formula.Subscript(F.Id(name), D((byte)index));

    private static Formula Square(Formula value) =>
        new Formula.Power(value, D(2));

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));
}
