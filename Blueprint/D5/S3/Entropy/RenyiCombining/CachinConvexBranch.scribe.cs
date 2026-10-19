using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexBranchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinConvexBranch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Riccati quotient gives the convex-branch elasticity comparison for every real parameter between zero and one quarter.",
        H("Positive-Parameter Convexity Certificate"),
        Blocks(
            Paragraph(Text("Write n = alpha - 1, with 0 < n <= 1/4. The auxiliary function is "
                + "C_n(z)=n sqrt(z) coth(n artanh(sqrt(z))), extended by C_n(0)=1. Set D_n(z)=C_n(z)+nz. "
                + "The analytic quotient and its exact initial jets provide a neighborhood where C_n''<0 and C_n'<-n. "
                + "The first-zero argument propagates the negative curvature across (0,1).")),
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
}
