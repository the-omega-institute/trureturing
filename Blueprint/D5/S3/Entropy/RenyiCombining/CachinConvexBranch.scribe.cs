using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexBranchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinConvexBranch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Riccati differential identity and a first-zero principle certify curvature of the binary Renyi quotient.",
        H("Riccati Curvature Mechanism"),
        Blocks(
            Paragraph(Text("Use artanh(t)=(log(1+t)-log(1-t))/2. For positive n and 0<z<1 define "
                + "C_n(z)=n sqrt(z) cosh(n artanh(sqrt(z)))/sinh(n artanh(sqrt(z))). "
                + "The total definition fills z=0 with one and also provides the n=0 quotient sqrt(z)/artanh(sqrt(z)). "
                + "This module's derivative certificates use positive n and interior z only. Set D_n=C_n+nz.")),
            Node("C_hasDerivAt", "The Riccati equation", Domain(Call("HasDerivAt", Call("C", N("n")),
                new Formula.Fraction(Add(Subtract(Multiply(Subtract(D(1), N("z")), Cvalue()), Pow(Cvalue(), 2)),
                    Multiply(Pow(N("n"), 2), N("z"))), Multiply(Multiply(D(2), N("z")), Subtract(D(1), N("z")))), N("z"))),
                "Direct differentiation gives 2z(1-z)C_n'=(1-z)C_n-C_n^2+n^2z. "
                + "All quotient denominators are nonzero in the stated domain."),
            Node("C_eq_power_quotient", "Agreement with the real-power quotient", PowerIdentity(),
                "Expanding sinh and cosh and using the logarithmic definition of real powers identifies the hyperbolic and power quotients."),
            Node("C_curvature_equation", "Twice-differentiated Riccati equation", Domain(Equal(
                Multiply(Multiply(Multiply(D(2), N("z")), Subtract(D(1), N("z"))), Cd(3)),
                Add(Multiply(Subtract(Add(Seq(Minus, D(3)), Multiply(D(7), N("z"))), Multiply(D(2), Cvalue())), Cd(2)),
                    Multiply(Multiply(D(2), Cd(1)), Subtract(D(1), Cd(1)))))),
                "Differentiating the Riccati identity twice gives "
                + "2z(1-z)C_n'''=(-3+7z-2C_n)C_n''+2C_n'(1-C_n'). "
                + "At a zero of C_n'', a negative C_n' forces the right side to be strictly negative."),
            Paragraph(Text("The generic first-zero lemmas use continuity on compact intervals to select the earliest point with nonnegative curvature. "
                + "The preceding negative curvature makes the companion first derivative decrease. "
                + "At the earliest zero the left difference quotients are nonnegative, while the Riccati equation requires a negative derivative. "
                + "This contradiction propagates any negative initial neighborhood across the whole open interval. "
                + "The positive-parameter certificate obtains that initial neighborhood from the analytic quotient jets and applies this mechanism.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("cachin-convex-branch-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula N(string name) => F.Id(name);
    private static Formula All(string name, Formula body) => Seq(Forall, Sp, N(name), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Domain(Formula body) => All("n", All("z", Imp(
        Seq(Lt(D(0), N("n")), Sp, Land, Sp, Member(N("z"), Call("Ioo", D(0), D(1)))), body)));
    private static Formula Pow(Formula value, byte degree) => new Formula.Power(value, D(degree));
    private static Formula Cvalue() => Call("C", N("n"), N("z"));
    private static Formula Cd(byte degree) => Call("iteratedDeriv", D(degree), Call("C", N("n")), N("z"));
    private static Formula PowerIdentity()
    {
        var domain = Seq(Lt(D(0), N("n")), Sp, Land, Sp, Member(N("t"), Call("Ioo", D(0), D(1))));
        var numerator = Multiply(Multiply(N("n"), N("t")), Add(PowerPlus(), PowerMinus()));
        var quotient = new Formula.Fraction(numerator, Subtract(PowerPlus(), PowerMinus()));
        return All("n", All("t", Imp(domain, Equal(Call("C", N("n"), Pow(N("t"), 2)), quotient))));
    }
    private static Formula PowerPlus() => new Formula.Power(Add(D(1), N("t")), N("n"));
    private static Formula PowerMinus() => new Formula.Power(Subtract(D(1), N("t")), N("n"));
}
