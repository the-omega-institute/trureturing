using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real-power elasticity transform equals the Riccati denominator elasticity in squared-bias coordinates.",
        H("Transport to Squared-Bias Elasticity"),
        Blocks(
            Paragraph(Text("Use the auxiliary functions C and D of the Riccati branch, and define D1(n,z)=deriv(C_n)(z)+n. "
                + "The Lean declaration for this function uses the subscript spelling D₁. "
                + "For 0<r<1 the bias t=(1-r)/(1+r) also belongs to (0,1).")),
            Describe.Lean(DescribeId.Create("cachin-convex-transport-elasticity-identity"),
                DeclarationHandle.Create("D5/S3/Entropy/RenyiCombining/CachinConvexTransport.F_eq_denominator_elasticity"),
                H("The two elasticity formulas agree"), StatementSource.FromAuthor(Disp(Identity())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The hyperbolic quotient gives C_n(t^2)=nt(1+r^n)/(1-r^n). "
                    + "Substitute this identity into A_n(r) and B_n(r), and use the Riccati derivative of C_n. "
                    + "The result identifies F_n(r) with 1-2zD_n'(z)/D_n(z), where z=t^2. "
                    + "All denominators are nonzero because n>0 and 0<r<1. "
                    + "The certificate for positive parameters combines this identity with monotonicity of the squared-bias elasticity."))),
                DescribeRole.Theorem))));

    private static Formula Identity()
    {
        var n = F.Id("n");
        var r = F.Id("r");
        var bias = new Formula.Fraction(Subtract(D(1), r), Add(D(1), r));
        var premise = Seq(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n), Sp, Land, Sp,
            new Formula.Relation(r, FormulaRelationOperator.MemberOf, Call("Ioo", D(0), D(1))));
        var rhs = Call("elasticity", Call("D", n), Call("D1", n), new Formula.Power(bias, D(2)));
        return Seq(Forall, Sp, n, Comma, Sp, Forall, Sp, r, Comma, Sp,
            new Formula.Logic(premise, FormulaLogicOperator.Implies, Equal(Call("F", n, r), rhs)));
    }
}
