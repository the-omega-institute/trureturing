using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBAffineFirstBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same original total response satisfies the affine first-label budget of source 162.2. Its two P2 estimates use one functional and the complete actual PB outer labels.",
        H("Original affine PB budgets"),
        Blocks(
            Helper("leading_budget", "Leading scalar budgets", LeadingStatement(),
                "For arbitrary real coefficients, the affine absolute-value bound implies the leading square-root bound. Reciprocal positive scaling and continuity include zero leading coefficients.", DescribeRole.Theorem),
            Helper("gram_shift", "The shared-direction Gram expansion", ShiftStatement(),
                "Symmetric bilinearity expands the affine determinant into its constant, linear and quadratic terms; the cubic and quartic terms cancel.", DescribeRole.Theorem),
            Helper("realPerp", "Projection off one real line", PerpStatement(),
                "For a unit eta this real-linear map removes its real inner-product component. In a complex representation the removed line is real, not complex.", DescribeRole.Definition),
            Helper("two_ended_budget", "Both ends of a norm budget", EndsStatement(),
                "A unit leading direction and the budget for every real t force equality of the two first-order norm corrections. Reciprocal scaling makes zero a differentiable minimum.", DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBAffineFirstBudget.gram"),
                H("The shared-readout Gram determinant"),
                StatementSource.FromAuthor(Disp(GramStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("J is the original real bilinear Jordan product; phi is a real-linear reading of the original labels. No normalization, nonzero mass or strict Gram positivity is required."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-affine-first-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_first_budget"),
                H("The actual first affine budget, source 162.2"),
                StatementSource.FromAuthor(Disp(FirstStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("E is any original real module, without a dimension, separability or completeness restriction. J is symmetric and unital; J(h,h)=u and J(h,p)=J(h,q)=J(p,q)=0. The same total D satisfies the full original PB identity. For this same phi, every original pair satisfies phi(D(a,b)) squared at most Bphi(a,b). The actual 161.4 supplier is D(s u+r h,t p+alpha(u+h))=rt q for all real t and alpha. These are exact hypotheses, not consequences here of raw A1-A3. The original faithful JC inclusion, accurate cone-to-state transfer and actual-anchor construction retain their upstream obligations.")),
                    Paragraph(Text("In the formula g=D(s u+r h,x), k=J(h,x), v=x-J(h,k), theta=s+r and Z=(1+s theta)x+r theta k. The expression v is exactly (I-Uh)x/2 when Uh=2Lh squared-I; no projection law for D is assumed. The two anchors may independently be (e,j) and (j,-e). All real coefficients, including negative r, r=0 and theta=0, and zero or degenerate objects remain included.")),
                    Paragraph(Text("At b=t p+alpha(u+h), PB uses nu=rt q-sx-rk and omega=st p+theta alpha(u+h)+g. Its actual outer pairs are (t(p+rq)-sx-rk+alpha(u+h),x+g+stp+theta alpha(u+h)) and (t(p-rq)+sx+rk+alpha(u+h),x-g-stp-theta alpha(u+h)). Applying the same phi to both original P2 budgets bounds their PB difference by the sum of their square roots. The complete PB right side is 2rt J(p,k)-2J(x,g)-2alpha r(tq+v); no commuting block is deleted.")),
                    Paragraph(Text("The determinant expansion has constant term Bphi(A,B), linear term twice alpha times theta phi(J(A,A))phi(J(n,B))+phi(J(n,A))phi(J(B,B))-phi(J(A,B))(phi(J(n,B))+theta phi(J(n,A))), and quadratic term alpha squared Bphi(n,B-theta A). Cubic and quartic terms cancel for every real theta. The proof extracts the leading coefficient by setting alpha=delta inverse, multiplying by positive delta and taking delta down to zero in explicit scalar polynomials and square roots. Continuity includes a zero leading coefficient. No limit of D at varying inputs is used.")),
                    Paragraph(Text("For every real alpha, a bound of abs(c-alpha d) by sqrt(p0+2alpha p1+alpha squared p2)+sqrt(q0+2alpha q1+alpha squared q2) therefore implies abs(d) at most sqrt(p2)+sqrt(q2). Substituting the two expanded Gram determinants gives the displayed actual original-D budget. Applying it to the vector readings in the next theorem gives source 163.4. This result does not assert source 163.1, the actual second frame, the complete affine commuting-zero row or the full 192.2 conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-affine-vector-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_vector_budget"),
                H("The actual fixed-vector budget, source 163.4"),
                StatementSource.FromAuthor(Disp(VectorStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Readout R represents every original label by a symmetric real-linear operator, maps u to the identity, preserves J on the whole original domain and supplies original P2 for every vector. It is the existing PBActualOuterBudget.Readout with known subspace top, not BDerivedInterface or SectorCertificate. Complex Hilbert representations are read as real inner-product spaces. The geometric conditions are norm(eta)=1, op(h)xi=-xi, op(h)eta=eta, op(q)xi=eta and inner(eta,op(p)xi)=0. They concern the known frame, not a desired output law. No continuity of op as a function of original labels or of D is required.")),
                    Paragraph(Text("Here Peta(z)=z-inner(eta,z)eta is the real perpendicular projection. The unnormalised vector xi+delta eta reads Bphi(n,W)=4 delta squared norm(Peta(op(W)xi+delta op(W)eta)) squared, while its reading of tq+v is 2delta(t+inner(eta,op(v)xi)). This uses the same vector functional for both actual budgets. Cancelling positive 2delta and taking delta down to zero only in fixed finite vector expressions gives the displayed inequality. The shared Z and every commuting block remain present.")),
                    Paragraph(Text("The actual_affine_first_budget theorem is used on the live path for every positive delta. The next theorem consumes both ends of this actual budget to obtain source 163.6 for either nonzero sign of r. The remaining steps toward 163.1 are binding both actual anchors in a complex representation, ordinary complex polarization without a selfadjointness restriction, reconstruction of both corners and faithful return to E. None is silently assumed or reported complete. Full 192.2 also retains the actual second-frame and affine commuting-zero-row obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-affine-anchor-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBAffineFirstBudget.actual_affine_anchor_identity"),
                H("The original fixed-output single-anchor identity, source 163.6"),
                StatementSource.FromAuthor(Disp(AnchorStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keep exactly the preceding original-label and readout hypotheses, additionally r nonzero and norm(op(p)xi)=1. All positive and negative real r remain allowed. For every real t the preceding theorem gives the original budget. With w=op(p)xi, zplus=Peta(op(Z+g)xi) and zminus=Peta(op(Z-g)xi), reciprocal scaling converts it to 2 abs(1+delta r A) at most norm(delta zplus-w)+norm(delta zminus+w), where A=inner(eta,op(v)xi). This inequality holds for every real delta, including zero.")),
                    Paragraph(Text("Subtract the left side to obtain an explicit differentiable function with a minimum at zero. Since norm(w)=1, Mathlib HasDerivAt.norm_sq and HasDerivAt.sqrt give derivatives -inner(w,zplus) and inner(w,zminus) for the two norm terms at zero. The absolute-value term has derivative 2rA there because its argument equals one. IsLocalMin.hasDerivAt_eq_zero then gives 2rA=inner(w,zminus)-inner(w,zplus). Orthogonality to eta removes the real projection, and the shared Z cancels, yielding the displayed identity. No derivative, limit, scaling law or additivity of D is used.")),
                    Paragraph(Text("This is the single-anchor real identity, not a complex operator identity or source 163.1. The unit-row r=0 branch of the eventual projection theorem remains an upstream original-response supplier. Both actual anchors, complex polarization, corner reconstruction and faithful return remain to be combined. The four-slot escape audit at https://github.com/the-omega-institute/trureturing/issues/28369 is unfinished; no freezing, atom coverage or full 192.2 completion is asserted."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Helper(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBAffineFirstBudget."+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula RealHilbert(Formula body) => All("H",I("Type"),Seq(
        OpenBracket,C("NormedAddCommGroup",I("H")),CloseBracket,
        OpenBracket,C("InnerProductSpace",Rl,I("H")),CloseBracket,body));
    private static Formula LeadingStatement()
    {
        Formula Poly(string pre) => Add(Add(I(pre+"zero"),Mul(Mul(N(2),I("a")),I(pre+"one"))),Mul(Sq(I("a")),I(pre+"two")));
        var premise=All("a",Rl,Le(Abs(Sub(I("c"),Mul(I("a"),I("d")))),Add(C("sqrt",Poly("p")),C("sqrt",Poly("q")))));
        Formula body=Imp(premise,Le(Abs(I("d")),Add(C("sqrt",I("ptwo")),C("sqrt",I("qtwo")))));
        foreach(var name in new[]{"qtwo","qone","qzero","ptwo","pone","pzero","d","c"}) body=All(name,Rl,body);
        return body;
    }
    private static Formula ShiftStatement()
    {
        var phi=I("phi"); var aa=I("A"); var bb=I("B"); var nn=I("n"); var th=I("theta"); var al=I("alpha");
        Formula Read(Formula x) => App(phi,x);
        Formula Gram(Formula x, Formula y) => C("gram",J,phi,x,y);
        var coefficient=Sub(Add(Mul(Mul(th,Read(Jj(aa,aa))),Read(Jj(nn,bb))),Mul(Read(Jj(nn,aa)),Read(Jj(bb,bb)))),
            Mul(Read(Jj(aa,bb)),Add(Read(Jj(nn,bb)),Mul(th,Read(Jj(nn,aa))))));
        var result=Eq(Gram(Add(aa,Sm(al,nn)),Add(bb,Sm(Mul(th,al),nn))),
            Add(Add(Gram(aa,bb),Mul(Mul(N(2),al),coefficient)),Mul(Sq(al),Gram(nn,Sub(bb,Sm(th,aa))))));
        var sym=All("x",E,All("y",E,Eq(Jj(I("x"),I("y")),Jj(I("y"),I("x")))));
        return ModuleBind(All("J",C("Bilinear",Rl,E,E,E),All("phi",C("LinearMap",Rl,E,Rl),
            All("A",E,All("B",E,All("n",E,All("theta",Rl,All("alpha",Rl,Imp(sym,result)))))))));
    }
    private static Formula PerpStatement() => RealHilbert(All("eta",I("H"),All("z",I("H"),
        Eq(C("realPerp",I("eta"),I("z")),Sub(I("z"),Sm(C("inner",I("eta"),I("z")),I("eta")))))));
    private static Formula EndsStatement()
    {
        var r=I("r"); var a=I("A"); var w=I("w"); var zp=I("zp"); var zm=I("zm"); var t=I("t");
        var budget=All("t",Rl,Le(Mul(Mul(N(2),Abs(r)),Abs(Add(t,a))),
            Add(Norm(Sub(zp,Sm(Mul(r,t),w))),Norm(Add(zm,Sm(Mul(r,t),w))))));
        var conditions=Conj(Imp(Eq(r,N(0)),I("False")),Eq(Norm(w),N(1)),budget);
        var result=Eq(Mul(Mul(N(2),r),a),Sub(C("inner",w,zm),C("inner",w,zp)));
        return RealHilbert(All("r",Rl,All("A",Rl,All("w",I("H"),All("zp",I("H"),All("zm",I("H"),Imp(conditions,result)))))));
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => Call(s,xs);
    private static Formula N(int n) => Num(n);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a, Formula b) => Equal(a,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Add(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Add(a,b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a,b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a,b);
    private static Formula Sm(Formula a, Formula b) => C("smul",a,b);
    private static Formula Sq(Formula a) => C("pow",a,N(2));
    private static Formula Abs(Formula a) => C("abs",a);
    private static Formula Norm(Formula a) => C("norm",a);
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula Rl => Seq(Mathbb,Grp(I("R")));
    private static Formula E => I("E");
    private static Formula J => I("J");
    private static Formula U => I("u");
    private static Formula Hh => I("h");
    private static Formula P => I("p");
    private static Formula Q => I("q");
    private static Formula Dd => I("D");
    private static Formula S => I("s");
    private static Formula Rr => I("r");
    private static Formula X => I("x");
    private static Formula T => I("t");
    private static Formula App(Formula f, params Formula[] xs) => C("apply",new[]{f}.Concat(xs).ToArray());
    private static Formula Jj(Formula a, Formula b) => App(J,a,b);
    private static Formula V => Sub(X,Jj(Hh,Jj(Hh,X)));
    private static Formula G => App(Dd,Add(Sm(S,U),Sm(Rr,Hh)),X);
    private static Formula Theta => Add(S,Rr);
    private static Formula Z => Add(Sm(Add(N(1),Mul(S,Theta)),X),Sm(Mul(Rr,Theta),Jj(Hh,X)));
    private static Formula W(bool plus) => Sub(plus ? Sub(Add(Z,G),Sm(Mul(Rr,T),P)) : Add(Sub(Z,G),Sm(Mul(Rr,T),P)),Sm(Mul(Mul(Rr,Theta),T),Q));
    private static Formula BaseAssumptions() => Conj(
        All("a",E,All("b",E,Eq(Jj(I("a"),I("b")),Jj(I("b"),I("a"))))),
        All("a",E,Eq(Jj(U,I("a")),I("a"))),Eq(Jj(Hh,Hh),U),
        Eq(Jj(Hh,P),N(0)),Eq(Jj(Hh,Q),N(0)),Eq(Jj(P,Q),N(0)),C("PB",J,Dd));
    private static Formula Anchor() => All("tau",Rl,All("alpha",Rl,
        Eq(App(Dd,Add(Sm(S,U),Sm(Rr,Hh)),Add(Sm(I("tau"),P),Sm(I("alpha"),Add(U,Hh)))),Sm(Mul(Rr,I("tau")),Q))));
    private static Formula ModuleBind(Formula body) => All("E",I("Type"),Seq(
        OpenBracket,C("AddCommGroup",E),CloseBracket,
        OpenBracket,C("Module",Rl,E),CloseBracket,body));
    private static Formula CommonBind(Formula body) =>
        All("J",C("Bilinear",Rl,E,E,E),All("u",E,All("h",E,All("p",E,All("q",E,
        All("D",C("Function",E,E,E),body))))));
    private static Formula GramStatement()
    {
        var phi=I("phi"); var a=I("a"); var b=I("b");
        return ModuleBind(All("J",C("Bilinear",Rl,E,E,E),All("phi",C("LinearMap",Rl,E,Rl),
            All("a",E,All("b",E,Eq(C("gram",J,phi,a,b),Sub(Mul(App(phi,Jj(a,a)),App(phi,Jj(b,b))),Sq(App(phi,Jj(a,b))))))))));
    }
    private static Formula FirstStatement()
    {
        var phi=I("phi");
        var p2=All("a",E,All("b",E,Le(Sq(App(phi,App(Dd,I("a"),I("b")))),C("gram",J,phi,I("a"),I("b")))));
        var result=Le(Mul(Mul(N(2),Abs(Rr)),Abs(App(phi,Add(Sm(T,Q),V)))),
            Add(C("sqrt",C("gram",J,phi,Add(U,Hh),W(true))),C("sqrt",C("gram",J,phi,Add(U,Hh),W(false)))));
        return ModuleBind(CommonBind(All("phi",C("LinearMap",Rl,E,Rl),All("s",Rl,All("r",Rl,
            All("x",E,All("t",Rl,Imp(Conj(BaseAssumptions(),p2,Anchor()),result))))))));
    }
    private static Formula VectorStatement()
    {
        var H=I("H"); var r=I("R"); var xi=I("xi"); var eta=I("eta");
        Formula Op(Formula a, Formula z) => C("op",r,a,z);
        Formula Inner(Formula a, Formula b) => C("inner",a,b);
        Formula Perp(Formula z) => Sub(z,Sm(Inner(eta,z),eta));
        var result=Le(Mul(Mul(N(2),Abs(Rr)),Abs(Add(T,Inner(eta,Op(V,xi))))),
            Add(Norm(Sub(Perp(Op(Add(Z,G),xi)),Sm(Mul(Rr,T),Op(P,xi)))),
                Norm(Add(Perp(Op(Sub(Z,G),xi)),Sm(Mul(Rr,T),Op(P,xi))))));
        var conditions=Conj(BaseAssumptions(),Anchor(),Eq(Norm(eta),N(1)),
            Eq(Op(Hh,xi),Sm(new Formula.Negate(N(1)),xi)),Eq(Op(Hh,eta),eta),Eq(Op(Q,xi),eta),Eq(Inner(eta,Op(P,xi)),N(0)));
        var body=CommonBind(All("R",C("Readout",H,J,U,Dd,C("top",C("Submodule",Rl,E))),
            All("s",Rl,All("r",Rl,All("xi",H,All("eta",H,All("x",E,All("t",Rl,Imp(conditions,result)))))))));
        return ModuleBind(All("H",I("Type"),Seq(OpenBracket,C("NormedAddCommGroup",H),CloseBracket,
            OpenBracket,C("InnerProductSpace",Rl,H),CloseBracket,body)));
    }
    private static Formula AnchorStatement()
    {
        var H=I("H"); var r=I("R"); var xi=I("xi"); var eta=I("eta");
        Formula Op(Formula a, Formula z) => C("op",r,a,z);
        Formula Inner(Formula a, Formula b) => C("inner",a,b);
        var result=Eq(Mul(Rr,Inner(eta,Op(V,xi))),Mul(new Formula.Negate(N(1)),Inner(Op(P,xi),Op(G,xi))));
        var conditions=Conj(BaseAssumptions(),Anchor(),Imp(Eq(Rr,N(0)),I("False")),
            Eq(Norm(eta),N(1)),Eq(Norm(Op(P,xi)),N(1)),
            Eq(Op(Hh,xi),Sm(new Formula.Negate(N(1)),xi)),Eq(Op(Hh,eta),eta),Eq(Op(Q,xi),eta),Eq(Inner(eta,Op(P,xi)),N(0)));
        var body=CommonBind(All("R",C("Readout",H,J,U,Dd,C("top",C("Submodule",Rl,E))),
            All("s",Rl,All("r",Rl,All("xi",H,All("eta",H,All("x",E,Imp(conditions,result))))))));
        return ModuleBind(All("H",I("Type"),Seq(OpenBracket,C("NormedAddCommGroup",H),CloseBracket,
            OpenBracket,C("InnerProductSpace",Rl,H),CloseBracket,body)));
    }

}
