using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalControlMarkedJumpDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original double-wall jump operators determine a normalized continuous marked law on each affine leg.",
        H("Original Continuous Marked Jump Law"),
        Blocks(Describe.Lean(
            DescribeId.Create("affine-marked-probability"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalControlMarkedJump.affine_marked_probability"),
            H("A complete marked probability law on an affine leg"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every interior preparation height a and every original phase, signed parity and mode phase vector, source_diagonal states normSq(source(c,a,beta,m,theta)(i))=p(c,a)(i). Its assumptions are c<1/2 and 0<a<c, for every one of the five modes. This equality identifies the original preparation diagonal used in native failure composition.")),
                    Paragraph(Text("Fix c below one half and positive heights x,y below c. A positive duration h gives the actual height k(t)=x+(y-x)*t/h. The five probabilities are (k,c-k,1-2*c,c-k,k), with the last coordinate retaining original mode13. Both directions and the stationary case are included. A constant real control phase has zero transported phase. No common duration or speed bound is imposed.")),
                Paragraph(Text("In the displayed statement h, k, c, x and y are duration(L), height(L), c(L), x(L) and y(L); base(L)=(c,c,1-2*c), S(t)=survival(L,t), mu=markedLaw(L), and nu(i)=modeMeasure(L,i). A set superscript c denotes its complement. OC, AC and FC mean OriginalControl, AbsolutelyContinuousOnInterval and FiniteC1Control, with exactly the displayed arguments. Record is Unit plus Fin5 times the real line; s is Sum.inl(). Its success singleton and all five time-labelled failure components are measurable.")),
                Paragraph(Text("H(L,chi,t,i) is the integral from zero to t of phaseWeight(base(L),k(u),i) times the derivative at u of the constant function chi. SuccessMass(L,beta,m,theta) is the sum over i:Fin5 of normSq of component i of successfulKraus(c,x,y,S(h)) applied to source(c,x,beta,m,theta). JumpMass(L,beta,m,theta,t,i) is normSq of component0 of jumpKraus(c,x,k(t),S(t),jumpRate(L,t),i) applied to that same source. FailureSection(L,E,i) is (0,h] intersected with the set of all t for which Sum.inr(i,t) belongs to E. lintegral(A,f) below uses Lebesgue measure restricted to A; ofReal is ENNReal.ofReal. These abbreviations retain exactly the successful vector and the absorbing row of the original operators.")),
                Paragraph(Text("The prepared input has middle amplitude sqrt(1-2*c). Each bottom amplitude is its positive probability square root times the negative exponential of its preparation angle plus an arbitrary common unknown phase. The two minus modes also carry the arbitrary integer parity factor. Thus every input of the original phase and parity family is retained, and its diagonal is exactly the original probability vector at x.")),
                Paragraph(Text("The actual hazard is the positive part of k prime divided by k, plus the positive part of minus k prime divided by c-k. Survival is defined by the exponential of minus the integral of this hazard. Integrating the appropriate logarithmic derivative gives x/k on an increasing leg, and (c-x)/(c-k) on a decreasing leg. The original mode jump rate is the hazard minus the derivative of log p_i(k). All five rates are nonnegative.")),
                Paragraph(Text("The successful operator is the original diagonal matrix with entries sqrt(S)*sqrt(p_i(k)/p_i(x)). The jump matrix is the absorbing row sqrt(g_i)*bra(i), multiplied by that successful matrix. Matrix action on the original prepared input gives squared absorbing amplitude g_i*S*p_i(k). Preparation phases cancel in this calculation; they are not chosen to simplify the input. The sum of the successful squared amplitudes is S.")),
                Paragraph(Text("Differentiating S*p_i(k) on a leg gives minus this mode density. Its integral is therefore p_i(x)-S(h)*p_i(y). Summing the five exact balances proves that the continuous failure mass is 1-S(h). The marked measure is the success atom of mass S(h), plus one density measure for every original mode on the entire continuous interval (0,h]. These measures have no failure atoms. Their total mass is one.")),
                Paragraph(Text("For every Borel set of records, the measure agrees with the sum of the actual squared Kraus outputs integrated over precisely its retained time and mode labels. The output space includes both terminal success and the complete continuous failure record. This is a finite-dimensional source-family statement. It makes no assertion about trace distance for arbitrary references or the common absorbing extension.")),
                Paragraph(Text("A repeated-prefix early and late construction additionally requires chronological assembly of these laws, equality of the literal common prefix on [0,1] in the duration2 controls, the exact suffix clocks, disjoint suffix failure supports, the event supremum in the probability convention of total variation, and the fixed positive height gap. Those conclusions, their resource equalities and the inverse obstruction do not follow merely from the affine-leg statement."))),
            DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var j = 0; j < arguments.Length; j++)
        {
            if (j > 0) items.Add(Comma);
            items.Add(arguments[j]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula A(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Q(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Statement()
    {
        Formula l=F.Id("L"), chi=F.Id("chi"), beta=F.Id("beta"), m=F.Id("m");
        Formula theta=F.Id("theta"), t=F.Id("t"), i=F.Id("i"), e=F.Id("E");
        Formula r=Seq(Mathbb,Grp(F.Id("R"))), z=Seq(Mathbb,Grp(F.Id("Z")));
        Formula fin=C("Fin",D(5)), h=C("duration",l), k=C("height",l);
        Formula c=C("c",l), x=C("x",l), y=C("y",l), mu=C("markedLaw",l);
        Formula interval=C("Ioc",D(0),h), nu=C("modeMeasure",l,i);
        Formula terminal=C("ofReal",C("SuccessMass",l,beta,m,theta));
        Formula density=Seq(t,Mapsto,Sp,C("ofReal",C("JumpMass",l,beta,m,theta,t,i)));
        Formula failures=Seq(new Formula.Subscript(Sum,Seq(i,Colon,Sp,fin)),Sp,
            C("lintegral",C("FailureSection",l,e,i),density));
        Formula survival=C("If",Seq(x,Leq,Sp,y),Q(x,A(k,t)),
            Q(Seq(c,Minus,x),Seq(c,Minus,A(k,t))));
        return Disp(Seq(Begin,Grp(F.Id("gathered")),
            Forall,Sp,l,Colon,F.Id("Leg"),Comma,Sp,chi,Comma,beta,Colon,r,Comma,
            Sp,m,Colon,z,Comma,Sp,theta,Colon,Seq(fin,To,Sp,r),Comma,RowBreak,Grp(),
            C("OC",C("base",l),h,k,C("const",chi)),Land,Sp,C("AC",k,D(0),h),Land,Sp,
            C("FC",h,k,C("const",chi)),Land,Sp,RowBreak,Grp(),
            Open,Forall,Sp,t,Colon,r,Comma,Sp,i,Colon,fin,Comma,
            C("H",l,chi,t,i),Eq,D(0),Close,Land,Sp,RowBreak,Grp(),
            Open,Forall,Sp,i,Colon,fin,Comma,Sp,t,Colon,r,Comma,
            A(nu,C("singleton",t)),Eq,D(0),Close,Land,Sp,
            Open,Forall,Sp,i,Colon,fin,Comma,A(nu,new Formula.Power(interval,F.Id("c"))),
            Eq,D(0),Close,Land,Sp,RowBreak,Grp(),
            Open,Forall,Sp,t,InMacro,Sp,C("Icc",D(0),h),Comma,
            C("survival",l,t),Eq,survival,Close,Land,Sp,C("IsProbabilityMeasure",mu),Land,Sp,
            RowBreak,Grp(),Open,Forall,Sp,e,Colon,C("Set",F.Id("Record")),Comma,
            C("MeasurableSet",e),Rightarrow,Sp,A(mu,e),Eq,
            C("If",Seq(F.Id("s"),InMacro,Sp,e),terminal,D(0)),Plus,failures,Close,
            End,Grp(F.Id("gathered"))));
    }
}
