using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualKernelLocalPrecisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPrecision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal arithmetic derivative and cusp controls for the actual complete kernel, including strict log convexity of its negative first derivative.",
        H("Actual arithmetic local precision controls"), Blocks(
            Describe.Lean(DescribeId.Create("actual-local-precision-third-derivative"),
                DeclarationHandle.Create(Prefix+"D3"),H("Literal third derivative expression"),
                StatementSource.FromAuthor(F.Disp(D3Formula())),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D3(t)=D1(t)/4-exp(t/2)/2-exp(-t/2)/(2*(exp(2*t)-1))-2*exp(3*t/2)/(exp(2*t)-1)^2. This definition is a new literal formula and is not an assumption about the actual K."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-local-precision-differentiate-d2"),
                DeclarationHandle.Create(Prefix+"hasDerivAt_D2"),H("Differentiate the actual second derivative"),
                StatementSource.FromAuthor(F.Disp(DerivativeFormula())),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every 0<t<log(2), the public D2 has derivative D3(t). The proof differentiates K(t)/4-exp(t/2)+exp(-t/2)/(exp(2*t)-1), using the actual public hasDerivAt_K and the strictly positive denominator. The exponential identity exp(3*t/2)=exp(-t/2)*exp(2*t) gives precisely the displayed expression."))),DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("actual-local-precision-common-window"),
                DeclarationHandle.Create(Prefix+"exists_derivative_control_window"),H("A common arithmetic derivative-control window"),
                StatementSource.FromAuthor(F.Disp(WindowFormula())),AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exists one 0<delta<log(2), with delta<=exp(-1), on which K(t)>=K(0)/2, D1(t)<0, 1/(4*t)<=D2(t)<=1/t, -D1(t)<=log(1/t), and both displayed logarithmic-curvature numerators are positive. The derivative identity for D2 holds throughout the open interval. Strict convexity of log(K) is proved on the CLOSED interval [0,delta], using continuity at 0; strict convexity of log(-D1) is proved on (0,delta), without assigning a continuous derivative value at 0.")),
                    Paragraph(Math(F.Disp(CurvatureLimits()))),
                    Paragraph(Text("All displayed limits are right limits as t approaches 0. The proof directly reuses ActualKernelLocalPositivity.exp_ratio_limit for t/(exp(2*t)-1)->1/2 and its weighted_D1_limit and weighted_D2_limit for the weighted derivative limits. The public log_argument_ratio_limit gives log(1-exp(-2*t))+log(1/t)->-log(1/2). Substituting into the literal D1 gives (-D1)/log(1/t)->1/2. The literal term multiplying exp(-t/2) is log(2*pi)+log(1-exp(-2*t))/2: log(2*pi) is not halved.")),
                    Paragraph(Math(F.Disp(LiteralD1()))),
                    Paragraph(Text("The proof separately derives t*D1(t)^2->0 from t*log(1/t)^2->0 and the normalized D1 limit. It does not infer this square estimate merely from t*D1(t)->0. Multiplying the reused t*D2(t)->1/2 by continuity of K yields t*(K*D2-D1^2)->K(0)/2. Differentiating D2 gives t^2*D3(t)->-1/2. With h=-D1, h'=-D2 and h''=-D3, the normalized h-curvature tends to 1/4.")),
                    Paragraph(Text("The private log-convexity helpers use the actual quotient derivative f'/f, the numerator f*f''-(f')^2, and Mathlib.strictConvexOn_of_deriv2_pos. The closed-endpoint K proof uses continuity of log(K) at 0 and differentiates only in the interior. Positivity of K(0) directly reuses ActualKernelLocalPositivity.K_zero_pos, with no RH premise.")),
                    Paragraph(Text("The arithmetic application uses v=K(0)-K, h=-D1 and g=D2. The generic module proves v(t)=integral from 0 to t of h, positivity and v(t)<=t*log(exp(1)/t), using logarithmic integrability and the actual endpoint limit of v. The positive-definite input is the existing public exists_window_posDef, whose conclusion is COMPLEX Matrix.PosDef. The transient example first applies real_posDef_of_complex and only then passes a real matrix to the generic criterion. Evenness follows from the public literal definition of K.")),
                    Paragraph(Math(F.Disp(ActualApplication()))),
                    Paragraph(Text("The derivative controls and both logarithmic convexities hold on one common local window. Together with real positive definiteness they imply the uniform four-node precision signs. They do not supply an arbitrary-dimensional precision theorem or a global representation."))),DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula R => F.Seq(F.Mathbb,F.Grp(I("R")));
    private static Formula T => I("t"); private static Formula D => I("delta");
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),domain,body);
    private static Formula Op(string name) => F.Seq(F.Operatorname,
        F.Grp(name.Split('.').SelectMany((s,i) => i==0 ? new[] { I(s) } : new[] { F.Dot,I(s) }).ToArray()));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Op(name),[.. xs]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a,FormulaLogicOperator.And,b));
    private static Formula K(Formula t) => Call("K",t);
    private static Formula D1(Formula t) => Call("D1",t);
    private static Formula D2(Formula t) => Call("D2",t);
    private static Formula D3(Formula t) => Call("D3",t);
    private static Formula Exp(Formula t) => Call("Real.exp",t);
    private static Formula Log(Formula t) => Call("Real.log",t);
    private static Formula Int(string kind) => Call("Set."+kind,N(0),D);
    private static Formula CurvK => Sub(Mul(K(T),D2(T)),Pow(D1(T),N(2)));
    private static Formula Curvh => Sub(Mul(Neg(D1(T)),Neg(D3(T))),Pow(Neg(D2(T)),N(2)));
    private static Formula Lambda(string name, Formula body) => F.Seq(F.Open,F.LambdaLower,F.Sp,I(name),F.Sp,
        F.Mapsto,F.Sp,body,F.Close);
    private static Formula D3Formula() => All("t",R,Eq(D3(T),
        Sub(Sub(Sub(Div(D1(T),N(4)),Div(Exp(Div(T,N(2))),N(2))),
            Div(Exp(Div(Neg(T),N(2))),Mul(N(2),Sub(Exp(Mul(N(2),T)),N(1))))),
            Div(Mul(N(2),Exp(Div(Mul(N(3),T),N(2)))),Pow(Sub(Exp(Mul(N(2),T)),N(1)),N(2))))));
    private static Formula DerivativeFormula() => All("t",R,Imp(And(Lt(N(0),T),Lt(T,Log(N(2)))),
        Call("HasDerivAt",Op("D2"),D3(T),T)));
    private static Formula WindowFormula()
    {
        var bounds=All("t",Int("Ioc"),And(Le(Div(K(N(0)),N(2)),K(T)),Lt(D1(T),N(0)),
            Le(Div(N(1),Mul(N(4),T)),D2(T)),Le(D2(T),Div(N(1),T)),Le(Neg(D1(T)),Log(Div(N(1),T))),
            Lt(N(0),CurvK),Lt(N(0),Curvh)));
        return Ex("delta",R,And(Lt(N(0),D),Lt(D,Log(N(2))),Le(D,Exp(Neg(N(1)))),bounds,
            All("t",Int("Ioo"),Call("HasDerivAt",Op("D2"),D3(T),T)),
            Call("StrictConvexOn",R,Int("Icc"),Lambda("t",Log(K(T)))),
            Call("StrictConvexOn",R,Int("Ioo"),Lambda("t",Log(Neg(D1(T)))))));
    }
    private static Formula Limit(Formula expression, Formula value) =>
        Call("Filter.Tendsto",Lambda("t",expression),Call("nhdsGT",N(0)),Call("nhds",value));
    private static Formula CurvatureLimits() => And(
        Limit(Div(Neg(D1(T)),Log(Div(N(1),T))),Div(N(1),N(2))),
        Limit(Mul(T,D2(T)),Div(N(1),N(2))),
        Limit(Mul(T,Pow(D1(T),N(2))),N(0)),
        Limit(Mul(Pow(T,N(2)),D3(T)),Neg(Div(N(1),N(2)))),
        Limit(Mul(T,CurvK),Div(K(N(0)),N(2))),
        Limit(Div(Mul(Pow(T,N(2)),Curvh),Log(Div(N(1),T))),Div(N(1),N(4))));
    private static Formula LiteralD1() => All("t",R,Eq(D1(T),Add(Sub(Div(K(T),N(2)),Exp(Div(T,N(2)))),
        Mul(Exp(Div(Neg(T),N(2))),Add(Log(Mul(N(2),Op("Real.pi"))),
            Div(Log(Sub(N(1),Exp(Neg(Mul(N(2),T))))),N(2)))))));
    private static Formula ActualApplication()
    {
        var fin=Call("Fin",N(4)); var x=I("x"); var i=I("i"); var j=I("j");
        var xi=new Formula.Apply(x,[i]); var xj=new Formula.Apply(x,[j]);
        var matrix=Lambda("i",Lambda("j",K(Sub(xi,xj))));
        var diameter=All("i",fin,All("j",fin,Le(new Formula.Absolute(Sub(xi,xj)),D)));
        var signs=All("i",fin,All("j",fin,Imp(Rel(i,FormulaRelationOperator.NotEqual,j),
            Lt(new Formula.Apply(Pow(matrix,Neg(N(1))),[i,j]),N(0)))));
        return Ex("delta",R,And(Lt(N(0),D),All("x",new Formula.TypeArrow(fin,R),
            Imp(And(Call("Function.Injective",x),diameter),signs))));
    }
}
