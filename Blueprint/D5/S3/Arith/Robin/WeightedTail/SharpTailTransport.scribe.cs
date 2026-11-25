using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.WeightedTail;

internal sealed class SharpTailTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit logarithmic transport for weighted tails",
        H("Normalized transport and its Robin application"),
        Blocks(
            Paragraph(Text("Use the existing tail(k,x) and weightedTail(k,x) from "
                + "Weil.Mertens.WeightedTailTransport. Their logarithmic weight is "
                + "r(t)=(1+log(t))/log(t)^2 and density(t)=-r'(t) on t>1. "
                + "Write D(x)=sqrt(x)*log(x).")),
            Describe.Lean(DescribeId.Create("normalized-tail-transport"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/WeightedTail/SharpTailTransport.normalized_tail_transport"),
                H("Explicit logarithmic transport error"),
                StatementSource.FromAuthor(Transport()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Absolute Fubini in WeightedTailTransport.transport gives "
                    + "tail(k,x)*r(x)-weightedTail(k,x) as the integral of density(t)*tail(k,t). "
                    + "After scaling and subtracting sqrt(x)*tail(k,x), the boundary term is "
                    + "sqrt(x)*tail(k,x)/log(x), of magnitude at most C/log(x). "
                    + "For t>=x>=2, density(t)/sqrt(t) is bounded by "
                    + "the derivative of -2/(sqrt(t)*log(t)^2). This derivative is nonnegative "
                    + "and its half-line integral is 2/(sqrt(x)*log(x)^2), by the improper "
                    + "fundamental theorem and the primitive's zero limit. The integrated error "
                    + "after scaling is therefore at most 2*C/log(x). The closed-tail hypothesis "
                    + "includes the boundary t=x. This estimate follows from the existing Fubini "
                    + "identity and the derivative comparison."))), DescribeRole.Theorem),
            new DocumentBlock.Section(H("Consequences at the Robin lower endpoint"), Blocks(
            Paragraph(Text("Write L=firstLiMass, J(x)=weightedTail(psiErrorKernel,x), and "
                + "G(v)=exp(-v/2)*U(exp(v)). The earlier RHSharpArithmeticEnvelope proves "
                + "sqrt(x)*Q(x)=-G(log(x)) for x>=2 (sqrt_Q), identifies J with Jpsi via "
                + "weighted_eq, and gives the signed limit D(x)*J(x)+G(log(x))->0 under RH "
                + "(Jpsi_signed_limit). The new estimate also gives this limit: "
                + "RHSharpActualEnvelope.actual_G_control and firstLiMass_lt_third "
                + "supply the eventual closed-tail bound with C=1/3. "
                + "For each epsilon>0, eventually |D(x)*J(x)|<L+epsilon by the triangle inequality. "
                + "The recurrence G(m)->L along arbitrarily late natural m, together with "
                + "the signed limit at x=exp(m), gives |D(exp(m))*J(exp(m))+L|<epsilon "
                + "arbitrarily far out.")),
            Paragraph(Text("For y=log(n), put F(n)=D(y)*robinLogMargin(n), "
                + "A(n)=D(y)*(robinLogMargin(n)-J(y)), S(n)=G(log(y)), and B=2*sqrt(2)-2. "
                + "For each eta>0, SharpReserveLower.sharp_lower_reserve_all_integers "
                + "gives A(n)>B-eta eventually since D(y)>0 on y>=16. Under RH, "
                + "RHSharpActualEnvelope.actual_G_control gives S(n)<L+eta and the signed limit gives "
                + "|E(y)|<eta, where E(y)=D(y)*J(y)+G(log(y)). "
                + "Use the maximum of these three thresholds. For any real delta with "
                + "F(n)<=B-L+delta, the identity F=A-S+E implies "
                + "B-eta<=A(n)<=B+delta+2*eta and "
                + "L-delta-2*eta<=S(n)<=L+eta. Thus both components approach their respective "
                + "endpoints along every sequence tending to infinity with F(n)->B-L. "
                + "The earlier RHSharpAllIntegerMargin.all_integer_sharp_margin "
                + "supplies the all-integer lower envelope and sharp attainment at strict "
                + "original records under RH.")))))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Transport()
    {
        var k = F.Id("k");
        var x = F.Id("x");
        var c = F.Id("C");
        var t = F.Id("t");
        var bound = All("t", Real, Imp(Le(x, t),
            Le(new Formula.Absolute(Call("tail", k, t)), new Formula.Fraction(c, Call("sqrt", t)))));
        var difference = Subtract(Multiply(Call("D", x), Call("weightedTail", k, x)),
            Multiply(Call("sqrt", x), Call("tail", k, x)));
        var conclusion = Le(new Formula.Absolute(difference),
            new Formula.Fraction(Multiply(D(3), c), Call("log", x)));
        return Disp(All("k", new Formula.TypeArrow(Real, Real), All("x", Real, All("C", Real,
            Imp(Le(D(2), x), Imp(Call("IntegrableOn", k, Call("Ioi", x)),
                Imp(bound, conclusion)))))));
    }
}
