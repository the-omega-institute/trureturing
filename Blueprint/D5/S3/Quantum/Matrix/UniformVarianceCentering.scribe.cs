using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class UniformVarianceCenteringDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform variance budget on every unit vector controls simultaneous block means and the full ambient centered Gram operator.",
        H("Uniform variance and block centering"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-variance-hermitian-block-centering-gram"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceCentering.hermitian_block_centering_and_gram_bound"),
            H("Simultaneous means and the ambient Gram bound"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H and G be arbitrary finite-dimensional complex Hilbert spaces, including the zero space. Let J be any finite index type, V a complex linear isometry from G into H, and h(j) Hermitian complex linear endomorphisms of H. Assume delta is nonnegative and the sum of squared ambient residuals h(j)Vx minus Re(inner(Vx,h(j)Vx))Vx is at most delta for every unit x in G.")),
                Paragraph(Text("Choose an anchor e in G. The anchor is required to have norm one only when G has a unit vector; in a zero block this requirement is vacuous. Define c(j)=Re(inner(Ve,h(j)Ve)), L(j)=h(j)V-c(j)V as a rectangular complex linear map from G into the whole ambient H, and Q=sum(j) L(j) adjoint composed with L(j).")),
                Paragraph(Text("For every unit x, the sum of squared mean displacements from the anchor is at most 4 delta and the sum of squared norms of L(j)x is at most 5 delta. For every vector x, with no normalization, Re(inner(x,Qx)) equals that same ambient energy and is at most 5 delta times norm(x) squared. The operator norm of the actual bounded operator Q is at most 5 delta. For every bounded complex linear endomorphism A of the full ambient H, the actual centered Kraus adjoint sum(j) L(j) adjoint composed with A composed with L(j) has operator norm at most 5 delta times the operator norm of A. This bound also holds at every finite reference size n: on the L2 sum of n copies, apply each same L(j) coordinatewise and allow every bounded complex linear A on the entire amplified ambient space, including operators coupling different reference coordinates.")),
                Paragraph(Text("The proof forms the real coefficient direction from the mean displacements. Cauchy-Schwarz controls its scalar variance. Compact Rayleigh extrema of the compressed symmetric operator are eigenvectors; their equal superposition bounds the spectral diameter. A Pythagorean expansion then separates variance from mean displacement. Applying the resulting bound to the actual rectangular residual maps gives the Gram estimate. Cauchy-Schwarz for the two residual-vector families then bounds every matrix coefficient of the centered Kraus adjoint and hence its operator norm. Summing the actual residual energy over reference coordinates preserves the same 5 delta constant, so the same argument applies at every finite reference size.")),
                Paragraph(Text("For a center block of a finite complex matrix direct sum, V is its canonical isometric inclusion and h(j) acts on the entire direct-sum Hilbert space. Thus all components transferred to other center blocks remain in L(j)x and Q. There is no hypothesis that the individual Kraus operators preserve a block. Applying this statement to each nonzero block uses its own anchor; zero factors contribute zero. No spectral simplicity, positive lower eigenvalue, dimension bound, or sum of Kraus squares is needed for this implication.")),
                Paragraph(Text("Ltwo(Fin(n),G) denotes the Hilbert L2 direct sum of n copies of G; the displayed defining equations specify the coordinatewise reference amplification uniquely. This is the all-vector implication from the variance hypothesis in C109 equation 86.3 to equation 86.4 and the compressed Gram bound. The passage from the same actual S/H CP-TNI branches to the normalized map, the derivation of equation 86.3 from its Hilbert-Schmidt spectral lower bound, and the Hermitian Kraus construction remain separate obligations. The actual centered rectangular family has the complete-reference trace-norm estimate of hermitian_centered_kraus_trace_bound in UniformVarianceTraceBound; the actual direct-sum construction and conditional global defect bound are given by hermitian_direct_sum_centering and hermitian_unital_direct_sum_defect_trace_bound. The original complete Theorem 86.1 is open. Mathematical block vectors and inclusions assert no operational preparation or additional process supply."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("uniform-variance-actual-direct-sum-centering"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceCentering.hermitian_direct_sum_centering"),
            H("The actual global direct sum and all its center transfers"),
            StatementSource.FromAuthor(Disp(DirectSumStatement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let I and J be arbitrary finite types and E(i) arbitrary finite-dimensional complex Hilbert spaces. The ambient H is the actual Hilbert L2 direct sum of the E(i). V(i) inserts a vector into coordinate i and P(i) projects onto that coordinate. The same arbitrary Hermitian h(j) acts on all of H. The variance assumption is required only for unit vectors in each individual input block, with every output component of h(j)V(i)x retained. Each anchor e(i) has norm one whenever its block admits a unit vector; zero blocks and empty index types are included.")),
                Paragraph(Text("Set c(j,i)=Re(inner(V(i)e(i),h(j)V(i)e(i))), c(j)=sum(i) c(j,i)P(i) and ell(j)=h(j)-c(j). For every natural reference size n, amplify these actual operators coordinatewise on Ltwo(Fin(n),H), and define B(j,i,k)=Ref(P(k)) Ref(ell(j)) Ref(P(i)). The theorem bounds the sum of squared norms of all these B(j,i,k)x by 5 delta norm(x) squared for every amplified vector x. It also bounds the actual Kraus adjoint sum(j,i,k) B adjoint A B in operator norm by 5 delta norm(A), for every complex bounded operator A on the full amplified space, including reference couplings.")),
                Paragraph(Text("The original coefficient-direction and extremal-superposition variance argument is consumed separately for each actual input inclusion. The squared norms are summed over the orthogonal output projections and then over input coordinates and reference coordinates. Thus transferred components are counted in their actual output blocks; no block-preservation hypothesis or mixed-center all-vector variance premise occurs. The original same-S/H construction and its delta=beta variance bridge remain open."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("uniform-variance-kraus-energy-adjoint-norm"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceCentering.kraus_adjoint_norm_le"),
            H("The operator bound from the actual Kraus energy"),
            StatementSource.FromAuthor(Disp(AdjointStatement())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For arbitrary finite-dimensional complex Hilbert input and output spaces, a finite rectangular family L and nonnegative b, a bound sum(j) norm(L(j)x) squared at most b on every unit input gives norm(sum(j) L(j) adjoint A L(j)) at most b norm(A) for every bounded ambient A. The direct-sum trace proof applies this Cauchy-Schwarz estimate to the actual transfer family and to the channel-contraction step."))),
            DescribeRole.Lemma))));

    private static Formula Statement()
    {
        var h = F.Id("h"); var v = F.Id("V"); var e = F.Id("e");
        var x = F.Id("x"); var j = F.Id("j"); var d = Delta;
        Formula M(Formula z) => RealPart(Inner(App(v,z), App(At(h,j),App(v,z))));
        var cj = At(F.Id("c"),j); var lj = At(F.Id("L"),j); var q = F.Id("Q");
        var variance = All("x", F.Id("G"), Implies(Unit(x),
            Leq(Sum("j",F.Id("J"),Sq(Norm(Sub(App(At(h,j),App(v,x)),Mul(M(x),App(v,x)))))),d)));
        var assumptions = And(
            All("j",F.Id("J"),Call("IsSymmetric",At(h,j))),
            And(Leq(D(0),d),And(variance,
                Implies(ExistsUnit(),Eqn(Norm(e),D(1))))));
        var definitions = And(All("j",F.Id("J"),Eqn(cj,M(e))),
            And(All("j",F.Id("J"),Eqn(lj,
                Sub(Mul(At(h,j),v),Mul(cj,v)))),
                Eqn(q,Sum("j",F.Id("J"),Mul(Adj(lj),lj)))));
        var unitBounds = All("x",F.Id("G"),Implies(Unit(x),And(
            Leq(Sum("j",F.Id("J"),Sq(Sub(M(x),cj))),Mul(D(4),d)),
            Leq(Energy(x),Mul(D(5),d)))));
        var gram = All("x",F.Id("G"),And(
            Eqn(RealPart(Inner(x,App(q,x))),Energy(x)),
            Leq(RealPart(Inner(x,App(q,x))),Mul(Mul(D(5),d),Sq(Norm(x))))));
        var cp = All("A",Call("ContinuousLinearMap",ComplexType(),F.Id("H"),F.Id("H")),
            Leq(Norm(Sum("j",F.Id("J"),Mul(Adj(lj),Mul(F.Id("A"),lj)))),
                Mul(Mul(D(5),d),Norm(F.Id("A")))));
        var n = F.Id("n"); var r = F.Id("r"); var rr = F.Id("R");
        var rg = Call("Ltwo",Call("Fin",n),F.Id("G"));
        var rh = Call("Ltwo",Call("Fin",n),F.Id("H"));
        var rj = At(rr,j);
        var rdef = All("j",F.Id("J"),All("x",rg,All("r",Call("Fin",n),
            Eqn(App(App(rj,x),r),App(lj,App(x,r))))));
        var references = All("n",Seq(Mathbb,Grp(F.Id("N"))),
            All("R",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),rg,rh)),
                Implies(rdef,All("A",Call("ContinuousLinearMap",ComplexType(),rh,rh),
                    Leq(Norm(Sum("j",F.Id("J"),Mul(Adj(rj),Mul(F.Id("A"),rj)))),
                        Mul(Mul(D(5),d),Norm(F.Id("A"))))))));
        var conclusion = All("c",Call("Family",F.Id("J"),RealType()),
            All("L",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("G"),F.Id("H"))),
            All("Q",Call("LinearMap",ComplexType(),F.Id("G"),F.Id("G")),
                Implies(definitions,And(unitBounds,And(gram,And(Leq(Norm(q),Mul(D(5),d)),And(cp,references))))))));
        var body = All("V",Call("LinearIsometry",ComplexType(),F.Id("G"),F.Id("H")),
            All("h",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("H"),F.Id("H"))),
            Seq(Forall,Sp,d,Colon,Sp,RealType(),Comma,Sp,
                All("e",F.Id("G"),Implies(assumptions,conclusion)))));
        return All("H",F.Id("Type"),All("G",F.Id("Type"),All("J",F.Id("Type"),
            Seq(Instances("H"),Comma,Sp,Instances("G"),Comma,Sp,
                OpenBracket,Call("Fintype",F.Id("J")),CloseBracket,Comma,Sp,body))));
    }

    private static Formula Conj(params Formula[] p)
    {
        var r=p[p.Length-1];
        for(var k=p.Length-2;k>=0;k--) r=And(p[k],r);
        return r;
    }
    private static Formula Quantify(Formula body,params (string,Formula)[] vars)
    {
        for(var k=vars.Length-1;k>=0;k--) body=All(vars[k].Item1,vars[k].Item2,body);
        return body;
    }
    private static Formula DirectSumBinders(Formula body)
    {
        var i=F.Id("i"); var ii=F.Id("I"); var ee=F.Id("E"); var jj=F.Id("J");
        Formula Cls(string name,params Formula[] tail) {
            var args=new System.Collections.Generic.List<Formula>();
            foreach(var item in tail) args.Add(item);
            args.Add(At(ee,i));
            return Seq(OpenBracket,Forall,Sp,i,Colon,Sp,ii,Comma,Sp,
                Call(name,args.ToArray()),CloseBracket,Sp);
        }
        return Quantify(Seq(OpenBracket,Call("Fintype",ii),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",ii),CloseBracket,Sp,
            Cls("NormedAddCommGroup"),Cls("InnerProductSpace",ComplexType()),
            Cls("FiniteDimensional",ComplexType()),OpenBracket,Call("Fintype",jj),CloseBracket,Sp,body),
            ("I",F.Id("Type")),("E",Call("Family",ii,F.Id("Type"))),("J",F.Id("Type")));
    }
    private static Formula DirectSumAssumptions(bool unital)
    {
        var i=F.Id("i"); var j=F.Id("j"); var x=F.Id("x"); var h=F.Id("h");
        var vi=Call("blockInclusion",F.Id("E"),i); var vx=App(vi,x); var hj=At(h,j);
        var ei=At(F.Id("E"),i); var anchor=At(F.Id("e"),i);
        var unitExists=Seq(Open,Exists,Sp,x,Colon,Sp,ei,Comma,Sp,Unit(x),Close);
        var variance=All("i",F.Id("I"),All("x",ei,Implies(Unit(x),
            Leq(Sum("j",F.Id("J"),Sq(Norm(Sub(App(hj,vx),
                Mul(RealPart(Inner(vx,App(hj,vx))),vx))))),Delta))));
        var sym=All("j",F.Id("J"),Call("IsSymmetric",hj));
        var anchors=All("i",F.Id("I"),Implies(unitExists,Unit(anchor)));
        if(unital) return Conj(sym,Eqn(Sum("j",F.Id("J"),Mul(hj,hj)),Call("Id",Call("Ltwo",F.Id("I"),F.Id("E")))),
            Leq(D(0),Delta),variance,anchors);
        return Conj(sym,Leq(D(0),Delta),variance,anchors);
    }

    private static Formula DirectSumStatement()
    {
        var i=F.Id("i"); var j=F.Id("j"); var t=F.Id("t"); var n=F.Id("n");
        var hspace=Call("Ltwo",F.Id("I"),F.Id("E"));
        var u=Call("Ltwo",Call("Fin",n),hspace);
        var end=Call("LinearMap",ComplexType(),u,u);
        var tt=Call("Product",F.Id("J"),F.Id("I"),F.Id("I"));
        var bt=At(F.Id("B"),t); var x=F.Id("x"); var a=F.Id("A");
        var tj=Call("first",t); var ti=Call("secondfirst",t); var tk=Call("secondsecond",t);
        Formula Proj(Formula z)=>Call("Ref",n,Call("blockProjection",F.Id("E"),z));
        var ell=Sub(At(F.Id("h"),tj),Call("centralMean",F.Id("h"),F.Id("e"),tj));
        var bdef=All("t",tt,Eqn(bt,Mul(Proj(tk),Mul(Call("Ref",n,ell),Proj(ti)))));
        var result=Conj(All("x",u,Leq(Sum("t",tt,Sq(Norm(App(bt,x)))),Mul(Mul(D(5),Delta),Sq(Norm(x))))),
            All("A",Call("ContinuousLinearMap",ComplexType(),u,u),
                Leq(Norm(Sum("t",tt,Mul(Adj(bt),Mul(a,bt)))),Mul(Mul(D(5),Delta),Norm(a)))));
        var body=All("n",Seq(Mathbb,Grp(F.Id("N"))),
            All("B",Call("Family",tt,end),Implies(bdef,result)));
        return DirectSumBinders(Seq(Forall,Sp,Delta,Colon,Sp,RealType(),Comma,Sp,Quantify(Implies(DirectSumAssumptions(false),body),
            ("h",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),hspace,hspace))),
            ("e",Call("Sections",F.Id("E"))))));
    }
    private static Formula AdjointStatement()
    {
        var l=At(F.Id("L"),F.Id("j")); var x=F.Id("x"); var b=F.Id("b"); var a=F.Id("A");
        var condition=Conj(Leq(D(0),b),All("x",F.Id("G"),Implies(Unit(x),
            Leq(Sum("j",F.Id("J"),Sq(Norm(App(l,x)))),b))));
        var body=Implies(condition,All("A",Call("ContinuousLinearMap",ComplexType(),F.Id("H"),F.Id("H")),
            Leq(Norm(Sum("j",F.Id("J"),Mul(Adj(l),Mul(a,l)))),Mul(b,Norm(a)))));
        return Quantify(Seq(Instances("H"),Sp,Instances("G"),Sp,
            OpenBracket,Call("Fintype",F.Id("J")),CloseBracket,Sp,
            Quantify(body,("L",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("G"),F.Id("H")))),
                ("b",RealType()))),("H",F.Id("Type")),("G",F.Id("Type")),("J",F.Id("Type")));
    }

    private static Formula Instances(string x) => Seq(
        OpenBracket,Call("NormedAddCommGroup",F.Id(x)),CloseBracket,Sp,
        OpenBracket,Call("InnerProductSpace",ComplexType(),F.Id(x)),CloseBracket,Sp,
        OpenBracket,Call("FiniteDimensional",ComplexType(),F.Id(x)),CloseBracket);
    private static Formula ExistsUnit() => Seq(Open,Exists,Sp,F.Id("x"),Colon,Sp,F.Id("G"),Comma,Sp,Unit(F.Id("x")),Close);
    private static Formula Energy(Formula x) => Sum("j",F.Id("J"),Sq(Norm(App(At(F.Id("L"),F.Id("j")),x))));
    private static Formula Unit(Formula x) => Eqn(Norm(x),D(1));
    private static Formula ComplexType() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula RealType() => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula All(string x,Formula t,Formula b) => Seq(Open,Forall,Sp,F.Id(x),Colon,Sp,t,Comma,Sp,b,Close);
    private static Formula Sum(string x,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(F.Id(x),InMacro,Sp,t),Sp,b);
    private static Formula At(Formula a,Formula i) => Seq(a,Underscore,Grp(i));
    private static Formula App(Formula a,Formula x) => Seq(a,Open,x,Close);
    private static Formula Adj(Formula a) => Seq(a,Caret,Grp(Star));
    private static Formula Inner(Formula a,Formula b) => Call("inner",a,b);
    private static Formula RealPart(Formula a) => Seq(Re,Open,a,Close);
    private static Formula Norm(Formula a) => Seq(Vert,Sp,a,Sp,Vert);
    private static Formula Sq(Formula a) => Seq(Open,a,Close,Caret,Grp(D(2)));
    private static Formula Mul(Formula a,Formula b) => Seq(a,Sp,b);
    private static Formula Sub(Formula a,Formula b) => Seq(a,Sp,Minus,Sp,b);
    private static Formula Leq(Formula a,Formula b) => Seq(a,Sp,Le,Sp,b);
    private static Formula Eqn(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula And(Formula a,Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula Implies(Formula a,Formula b) => Seq(Open,Open,a,Close,Sp,Rightarrow,Sp,Open,b,Close,Close);
    private static Formula Call(string n,params Formula[] a)
    {
        var parts = new System.Collections.Generic.List<Formula> { Operatorname,Grp(F.Id(n)),Open };
        for (int i=0;i<a.Length;i++) { if (i>0) parts.Add(Comma); parts.Add(a[i]); }
        parts.Add(Close); return Seq(parts.ToArray());
    }
}
