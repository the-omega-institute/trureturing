using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinConvexCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Riccati quotient gives the convex-branch elasticity comparison for every real parameter between zero and one quarter.",
        H("Positive-Parameter Convexity Certificate"),
        Blocks(
            Paragraph(Text("Write n = alpha - 1, with 0 < n <= 1/4. The auxiliary function is "
                + "C_n(z)=n sqrt(z) coth(n artanh(sqrt(z))), extended by C_n(0)=1. Set D_n(z)=C_n(z)+nz. "
                + "The analytic quotient and its exact initial jets provide a neighborhood where C_n''<0 and C_n'<-n. "
                + "The first-zero argument propagates the negative curvature across (0,1).")),
            Node("C_secondDeriv_neg", "Strict negative curvature", Domain(
                ForZ(Lt(Cderiv(2), D(0)))),
                "At a first zero of C_n'', the twice-differentiated Riccati identity forces C_n'''<0, "
                + "contradicting the nonnegative left derivative at that first crossing."),
            Node("D_hasDerivAt", "Derivative of the denominator", PositiveParameter(ForZ(
                Call("HasDerivAt", Call("D", N("n")), Call("D1", N("n"), N("z")), N("z")))),
                "D1(n,z) is defined as deriv(C_n)(z)+n. Differentiating D_n=C_n+nz gives this derivative."),
            Node("D1_hasDerivAt", "Derivative of the denominator slope", PositiveParameter(ForZ(
                Call("HasDerivAt", Call("D1", N("n")), Cderiv(2), N("z")))),
                "The derivative of D1 is C_n'', which is strictly negative in the required parameter range."),
            Node("D1_neg", "Strict decrease of the denominator", Domain(ForZ(
                Lt(Call("D1", N("n"), N("z")), D(0)))),
                "The denominator slope is strictly decreasing. Its negative initial neighborhood therefore forces it to remain negative everywhere."),
            Node("elasticity_strictMonoOn", "Strict increase of squared-bias elasticity", Domain(
                Call("StrictMonoOn", Call("elasticity", Call("D", N("n")), Call("D1", N("n"))),
                    Call("Ioo", D(0), D(1)))),
                "For E(z)=1-2zD'(z)/D(z), differentiation gives "
                + "E'=-2D'/D-2zD''/D+2z(D')^2/D^2. The first two terms are positive, and the last is nonnegative."),
            Node("antitoneOn_F", "Decrease of the original elasticity transform", Domain(
                Call("AntitoneOn", Call("F", N("n")), Call("Ioo", D(0), D(1)))),
                "The real-power transform F(n,r) equals the denominator elasticity at z=((1-r)/(1+r))^2. "
                + "That coordinate decreases with r, so the strictly increasing squared-bias elasticity gives antitonicity of F. "
                + "This is the positive-parameter certificate consumed by the convex clause of Hirche's Conjecture IV.18."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("cachin-convex-certificate-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula N(string name) => F.Id(name);
    private static Formula All(string name, Formula body) => Seq(Forall, Sp, N(name), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => new Formula.Logic(premise, FormulaLogicOperator.Implies, body);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Domain(Formula body) => All("n", Imp(Seq(Lt(D(0), N("n")), Sp, Land, Sp,
        new Formula.Relation(N("n"), FormulaRelationOperator.LessThanOrEqual, new Formula.Fraction(D(1), D(4)))), body));
    private static Formula PositiveParameter(Formula body) => All("n", Imp(Lt(D(0), N("n")), body));
    private static Formula ForZ(Formula body) => All("z", Imp(new Formula.Relation(N("z"), FormulaRelationOperator.MemberOf,
        Call("Ioo", D(0), D(1))), body));
    private static Formula Cderiv(int order) => Call("iteratedDeriv", D((byte)order), Call("C", N("n")), N("z"));
}
