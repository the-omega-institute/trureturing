using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBFixedOutputGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar fixed-output PB family forces a transverse output identity. The representation has no total-response or separate P2 hypothesis.",
        H("Fixed-output scalar PB and full vector Gram budgets"),
        Blocks(
            D("scalarPB", "The original scalar budget", ScalarStatement(),
                "For a fixed t, k and g, kappa and rho are the known commutator and Jordan rows. At the original probe x, put h=kappa(x)-k and r=rho(x)+g. The same real-linear functional reads L=-2(J(x,h)+J(t,r)) and both budgets. The determinant is the uncentered real Gram determinant phi(J(U,U))phi(J(W,W))-phi(J(U,W)) squared. No unknown outer response is introduced.", DescribeRole.Definition),
            D("SpectralPair", "A known spectral pair", PairStatement(),
                "The pair consists of e, j, n and real mu, lambda satisfying the six displayed relations. In a matrix spectral pair n=2l, lambda is half the difference of the two actor eigenvalues, and mu is half their sum. These relations describe known products and commutators. They impose no condition on the unknown fixed output g.", DescribeRole.Definition),
            D("VectorModel", "A full Jordan representation", ModelStatement(),
                "The real-linear operator map represents each label by a symmetric operator and represents the Jordan product by the symmetrized composition. H is the whole representation space. No restriction to the actor subspace is built into it, and no P2 field occurs.", DescribeRole.Definition),
            D("vectorReading", "One common vector reading", ReadingStatement(),
                "Every vector v of the full H defines a real-linear reading. Symmetry and the represented Jordan law give vectorReading(v,J(a,b))=inner(op(a)v,op(b)v). The corresponding determinant is therefore a real Gram determinant, including degenerate and zero values.", DescribeRole.Definition),
            D("fixed_output_anchor_identity", "The scalar PB transverse identity", AnchorStatement(),
                "Let a=mu+lambda, V=a J(n,t)-J(n,k) and Z=t+a k. Assume the original scalar PB for every unit vector reading on the full space and every probe T e+alpha n. The known support relation J(n,V)=V makes the V diagonal readings vanish on the zero and two eigenspaces of n. The relation J(n,j)=j gives the same fact for j. Both signs of nonzero lambda and d are retained.", DescribeRole.Theorem,
                "First expand the original PB at T e+alpha n. The affine Gram shift and the leading-coefficient estimate from PBAffineFirstBudget give 2 abs(phi(lambda T j+V)) at most the sum of the square roots of Bphi(n,Z+g-lambda T e-a lambda T j) and Bphi(n,Z-g+lambda T e-a lambda T j). The expansion remains valid when a leading budget vanishes.",
                "For unit xi, symmetry of n makes xi orthogonal to eta. Put b=1/sqrt(1+epsilon squared). The vector b(xi+epsilon eta) is unit. Its reading of lambda T j+V is exactly 2 epsilon b squared times lambda T d+inner(eta,op(V)xi). Its Gram determinant against n is exactly 4 epsilon squared b to the fourth times the squared norm of the real perpendicular projection of op(W)xi+epsilon op(W)eta. The square-root factor is exactly 2 epsilon/(1+epsilon squared). Cancel that common positive factor before taking epsilon down to zero with T fixed. The projected j term vanishes and the projected e term is d nu. Thus 2 abs(lambda T d+A) is at most norm(zplus-lambda T d nu)+norm(zminus+lambda T d nu), with A=inner(eta,op(V)xi) and zplus,zminus the projected readings of Z+g,Z-g.",
                "The existing two-ended norm estimate now yields 2 A=inner(nu,zminus)-inner(nu,zplus). Orthogonality removes the projection and the common Z cancels, giving inner(nu,op(g)xi)=-A. All vector and operator expressions remain on the full H, including complementary environment components. The companion-axis theorem combines two such identities. A concrete four-dimensional diagonal-residual conclusion additionally requires complex polarization, the full-row reconstruction and their matrix specialization."),
            D("fixed_output_two_axis_identity", "The two-axis complex identity", TwoAxisStatement(),
                "Use the same scalar PB for both probe families T e+alpha n and T j+alpha n. The additional known relations are kappa(j)=-lambda e, rho(j)=mu j and J(n,e)=e. The second spectral pair is constructed as (eprime,jprime,n)=(j,-e,n), keeping the same mu and lambda. Its vectors are etaprime=-nu and nuprime=eta, where nu=-iota eta and iota is either i or -i. Both vectors remain in the two eigenspace of n.", DescribeRole.Theorem,
                "The first real identity gives Re inner(nu,g xi)=-Re inner(eta,V xi). The constructed companion gives Re inner(eta,g xi)=Re inner(nu,V xi). The complex inner product is conjugate-linear in its first entry. Since inner(nu,z)=iota inner(eta,z), the two real readings determine the real and imaginary parts of inner(eta,g xi)=iota inner(eta,V xi), for either orientation. This is a pointwise full-space identity under the displayed representation and spectral hypotheses. The concrete M4 carrier and positive-functional transfer are given in PBFixedOutputM4. The primitive matrix spectral geometry and row reconstruction are separate from this abstract statement."))));

    private static DocumentBlock D(string name, string title, Formula formula, string text,
        DescribeRole role, params string[] more) => Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFixedOutputGram."+name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(new[]{Paragraph(Text(text))}.Concat(more.Select(s=>Paragraph(Text(s)))).ToArray()), role);
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
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Abs(Formula a) => C("abs",a);
    private static Formula Norm(Formula a) => C("norm",a);
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula Rl => Seq(Mathbb,Grp(I("R")));
    private static Formula E => I("E");
    private static Formula Hh => I("H");
    private static Formula J => I("J");
    private static Formula K => I("kappa");
    private static Formula Q => I("rho");
    private static Formula R => I("R");
    private static Formula P => I("F");
    private static Formula T => I("t");
    private static Formula B => I("k");
    private static Formula G => I("g");
    private static Formula Xi => I("xi");
    private static Formula Eta => I("eta");
    private static Formula Nu => I("nu");
    private static Formula Delta => I("d");
    private static Formula Field(string s) => C(s,P);
    private static Formula Eaxis => Field("e");
    private static Formula Jaxis => Field("j");
    private static Formula Na => Field("n");
    private static Formula Mu => Field("mu");
    private static Formula Lam => Field("lambda");
    private static Formula A => Add(Mu,Lam);
    private static Formula App(Formula f, params Formula[] xs) => C("apply",new[]{f}.Concat(xs).ToArray());
    private static Formula Jj(Formula a, Formula b) => App(J,a,b);
    private static Formula Op(Formula a, Formula z) => C("op",R,a,z);
    private static Formula Inn(Formula a, Formula b) => C("inner",a,b);
    private static Formula V => Sub(Sm(A,Jj(Na,T)),Jj(Na,B));
    private static Formula Reading(Formula z, Formula a) => C("vectorReading",R,z,a);
    private static Formula Base(Formula body) => All("E",I("Type"),Seq(OpenBracket,C("AddCommGroup",E),CloseBracket,
        OpenBracket,C("Module",Rl,E),CloseBracket,All("J",C("Bilinear",Rl,E,E,E),body)));
    private static Formula RealH(Formula body) => All("H",I("Type"),Seq(OpenBracket,C("NormedAddCommGroup",Hh),CloseBracket,
        OpenBracket,C("InnerProductSpace",Rl,Hh),CloseBracket,body));
    private static Formula Rows(Formula body) => All("kappa",C("LinearMap",Rl,E,E),All("rho",C("LinearMap",Rl,E,E),body));
    private static Formula Labels(Formula body) => All("t",E,All("k",E,All("g",E,body)));
    private static Formula Nonzero(Formula a) => Imp(Eq(a,N(0)),I("False"));
    private static Formula Scalar(Formula x, Formula phi)
    {
        var h=Sub(App(K,x),B); var r=Add(App(Q,x),G);
        return Le(Abs(App(phi,Sm(Neg(N(2)),Add(Jj(x,h),Jj(T,r))))),
            Add(C("sqrt",C("gram",J,phi,Add(x,h),Add(T,r))),
                C("sqrt",C("gram",J,phi,Sub(x,h),Sub(T,r)))));
    }
    private static Formula ScalarStatement() => Base(Rows(Labels(All("x",E,All("phi",C("LinearMap",Rl,E,Rl),
        new Formula.Logic(C("scalarPB",J,K,Q,T,B,G,I("x"),I("phi")),FormulaLogicOperator.Iff,Scalar(I("x"),I("phi"))))))));
    private static Formula PairStatement() => Base(Rows(All("F",C("SpectralPair",J,K,Q),Conj(
        Eq(App(K,Eaxis),Sm(Lam,Jaxis)),Eq(App(K,Na),N(0)),
        Eq(App(Q,Eaxis),Sm(Mu,Eaxis)),Eq(App(Q,Na),Sm(A,Na)),
        Eq(Jj(Eaxis,Jaxis),N(0)),Eq(Jj(Na,Jaxis),Jaxis)))));
    private static Formula ModelStatement() => Base(RealH(All("R",C("VectorModel",Hh,J),Conj(
        All("a",E,C("IsSymmetric",C("op",R,I("a")))),
        All("a",E,All("b",E,Eq(C("op",R,Jj(I("a"),I("b"))),
            Sm(C("divide",N(1),N(2)),Add(C("comp",C("op",R,I("a")),C("op",R,I("b"))),
                C("comp",C("op",R,I("b")),C("op",R,I("a"))))))))))));
    private static Formula ReadingStatement() => Base(RealH(All("R",C("VectorModel",Hh,J),All("v",Hh,All("a",E,
        Eq(Reading(I("v"),I("a")),Inn(I("v"),Op(I("a"),I("v")))))))));
    private static Formula TwoAxisStatement()
    {
        var probe=Add(Sm(I("tau"),Eaxis),Sm(I("alpha"),Na));
        var second=Add(Sm(I("tau"),Jaxis),Sm(I("alpha"),Na));
        var pb=All("v",Hh,Imp(Eq(Norm(I("v")),N(1)),All("tau",Rl,All("alpha",Rl,And(
            C("scalarPB",J,K,Q,T,B,G,probe,C("vectorReading",R,I("v"))),
            C("scalarPB",J,K,Q,T,B,G,second,C("vectorReading",R,I("v"))))))));
        var io=I("iota"); var nu=Sm(Neg(io),Eta);
        var orient=new Formula.Logic(Eq(io,I("i")),FormulaLogicOperator.Or,Eq(io,Neg(I("i"))));
        var conditions=Conj(All("a",E,All("b",E,Eq(Jj(I("a"),I("b")),Jj(I("b"),I("a"))))),
            Eq(App(K,Jaxis),Sm(Neg(Lam),Eaxis)),Eq(App(Q,Jaxis),Sm(Mu,Jaxis)),Eq(Jj(Na,Eaxis),Eaxis),
            pb,orient,Nonzero(Delta),Nonzero(Lam),Eq(Norm(Xi),N(1)),Eq(Norm(Eta),N(1)),
            Eq(Op(Na,Xi),N(0)),Eq(Op(Na,Eta),Sm(N(2),Eta)),Eq(Op(Na,nu),Sm(N(2),nu)),
            Eq(Op(Jaxis,Xi),Sm(Delta,Eta)),Eq(Op(Eaxis,Xi),Sm(Delta,nu)),Eq(Jj(Na,V),V));
        var result=Eq(C("complexInner",Eta,Op(G,Xi)),Mul(io,C("complexInner",Eta,Op(V,Xi))));
        var complex=Seq(Mathbb,Grp(I("C")));
        var body=Rows(All("F",C("SpectralPair",J,K,Q),All("R",C("VectorModel",C("realUnderlying",Hh),J),Labels(
            All("iota",complex,All("xi",Hh,All("eta",Hh,All("d",Rl,Imp(conditions,result)))))))));
        return Base(All("H",I("Type"),Seq(OpenBracket,C("NormedAddCommGroup",Hh),CloseBracket,
            OpenBracket,C("InnerProductSpace",complex,Hh),CloseBracket,body)));
    }
    private static Formula AnchorStatement()
    {
        var probe=Add(Sm(I("tau"),Eaxis),Sm(I("alpha"),Na));
        var pb=All("v",Hh,Imp(Eq(Norm(I("v")),N(1)),All("tau",Rl,All("alpha",Rl,C("scalarPB",J,K,Q,T,B,G,probe,C("vectorReading",R,I("v")))))));
        var conditions=Conj(All("a",E,All("b",E,Eq(Jj(I("a"),I("b")),Jj(I("b"),I("a"))))),pb,
            Nonzero(Delta),Nonzero(Lam),Eq(Norm(Xi),N(1)),Eq(Norm(Eta),N(1)),Eq(Norm(Nu),N(1)),
            Eq(Op(Na,Xi),N(0)),Eq(Op(Na,Eta),Sm(N(2),Eta)),
            Eq(Op(Jaxis,Xi),Sm(Delta,Eta)),Eq(Op(Eaxis,Xi),Sm(Delta,Nu)),
            Eq(Inn(Eta,Nu),N(0)),Eq(Jj(Na,V),V));
        var result=Eq(Inn(Nu,Op(G,Xi)),Neg(Inn(Eta,Op(V,Xi))));
        return Base(RealH(Rows(All("F",C("SpectralPair",J,K,Q),All("R",C("VectorModel",Hh,J),Labels(
            All("xi",Hh,All("eta",Hh,All("nu",Hh,All("d",Rl,Imp(conditions,result)))))))))));
    }
}
