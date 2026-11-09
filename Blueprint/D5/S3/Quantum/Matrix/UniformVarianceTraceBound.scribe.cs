using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class UniformVarianceTraceBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A variance budget controls the actual centered Kraus output in ordinary trace norm at every finite reference size.",
        H("Centered Kraus trace norm on finite references"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-variance-centered-kraus-trace-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_centered_kraus_trace_bound"),
            H("The actual rectangular centered family"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E and F be arbitrary finite-dimensional complex Hilbert spaces, J any finite type, V a complex linear isometric inclusion of E into F, and h(j) Hermitian endomorphisms of the whole ambient F. Suppose delta is nonnegative and the sum of squared ambient variances is at most delta for every unit vector of E. Choose e in E with norm one whenever E admits a unit vector. Set c(j)=Re(inner(Ve,h(j)Ve)) and L(j)=h(j)V-c(j)V. No component of L(j) in the ambient space is discarded.")),
                Paragraph(Text("For each natural reference size n, amplify each same L(j) coordinatewise on the Hilbert L2 sum of n copies. Let v and w be the standard orthonormal bases chosen by stdOrthonormalBasis for these amplified input and output spaces, and M(j) the rectangular matrix of that amplified map. Every complex input matrix X satisfies traceNorm(sum(j) M(j) X M(j) adjoint) at most 5 delta traceNorm(X). The norm is Re Tr sqrt(X adjoint X), with ordinary trace and no factor of one half. Inputs may be non-Hermitian and reference coordinates may be coupled. The empty Kraus family, zero-dimensional spaces, and n=0 are included.")),
                Paragraph(Text("The simultaneous block-centering theorem supplies the 4 delta expectation displacement and 5 delta ambient energy estimates through the coefficient direction and an equal superposition of extremal eigenvectors. Its actual amplified Kraus adjoint has operator norm at most 5 delta times the test operator norm. Unitary trace-norm duality and a singular-value expansion transfer that inequality to the actual matrix Kraus output. Orthonormal coordinates preserve the operator norm; no dimension comparison of matrix norms is used.")),
                Paragraph(Text("Ltwo(Fin(n),E) denotes the Hilbert L2 sum, stdBasis denotes stdOrthonormalBasis, and Ref(n,L) is the complex linear map satisfying Ref(n,L)(x)(r)=L(x(r)). MatrixOf(v,w,R) is LinearMap.toMatrix in the indicated orthonormal bases. FiniteRank is the complex dimension. The anchor condition is vacuous in the zero input space. This result proves the complete-reference trace-norm bridge for one actual centered rectangular family. The conditional global center-pinched map and its defect identity are constructed by hermitian_unital_direct_sum_defect_trace_bound. Obtaining the variance premise from the same S/H selected branches and unreferenced normalized return error, and proving the full local and whole-family bounds of original Theorem 86.1 remain separate obligations."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("uniform-variance-actual-factor-defect-trace-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_unital_kraus_defect_trace_bound"),
            H("The actual defect of a unital Hermitian factor family"),
            StatementSource.FromAuthor(Disp(DefectStatement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E be an arbitrary finite-dimensional complex Hilbert space and h(j) Hermitian endomorphisms with sum(j) h(j) composed with h(j) equal to the identity. Assume the same all-unit-vector variance budget delta and anchor condition as above. For every reference size n, H(j) is the matrix of the coordinatewise amplification of the same h(j). With c(j)=Re(inner(e,h(j)e)), M(j)=H(j)-c(j)I and Q=sum(j) M(j) adjoint M(j), the displayed centered defect identity holds for every complex input X.")),
                Paragraph(Text("The identity follows by expanding the actual M(j): the scalar linear terms and quadratic scalar terms cancel in the anticommutator minus the Kraus output. Unitality replaces sum(j) H(j) squared by I. The centered Gram norm is at most 5 delta. Testing the exact defect against a maximizing unitary bounds its two anticommutator terms by 5 delta traceNorm(X) each and its centered Kraus term by 5 delta traceNorm(X); the factor one half gives the stated 10 delta bound. No state restriction, reference dimension, rank factor, or least eigenvalue occurs.")),
                Paragraph(Text("This statement concerns a full matrix factor and includes zero E, empty J whenever its unitality premise holds, and n=0. It does not construct the source CP-TNI selected family or infer the variance premise from beta. Center-dependent scalars in a direct sum require the actual center pinching and its transfer terms; those are outside this factor statement."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("uniform-variance-actual-global-direct-sum-defect"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceTraceBound.hermitian_unital_direct_sum_defect_trace_bound"),
            H("The same globally pinched family on every finite reference"),
            StatementSource.FromAuthor(Disp(GlobalStatement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be the actual Hilbert direct sum of an arbitrary finite family of finite-dimensional complex spaces E(i). The same arbitrary Hermitian ambient family h(j) satisfies sum(j) h(j) squared equals I. Assume a nonnegative delta and the ambient variance bound for every unit vector within each input block; no variance premise on vectors mixing centers is imposed. The block anchors are unit whenever their block is nonzero. The theorem quantifies over every natural reference size n, including zero, and every complex input X commuting with all actual amplified center projections P(i). This is exactly the amplified original direct-sum algebra, with arbitrary off-diagonal reference entries.")),
                Paragraph(Text("At each reference, H(j) is the matrix of Ref(h(j)), M(j) the matrix of the same Ref(ell(j)), and C(Y)=sum(i) P(i)Y P(i). The center-dependent c(j) and ell(j)=h(j)-c(j) are those of the centering theorem. Set Q=C(sum(j) M(j) squared), A(j,i,k)=P(k)H(j)P(i), B(j,i,k)=P(k)M(j)P(i), Phi(X)=C(sum(j) H(j)XH(j)), and K(X)=C(sum(j) M(j)XM(j)). These are actual formulas, not assumed conclusions or fields of an auxiliary model.")),
                Paragraph(Text("The conclusions are Q at most 5 delta I in matrix order; sum A adjoint A equals I; sum B adjoint B equals Q; ordinary trace preservation of C on every ambient matrix, and commutation of C(Y) with every P(i). Thus the actual pinching has its range in the original direct-sum algebra. For every legal X, K(X)=sum B X B adjoint, Phi(X)=sum A X A adjoint, X-Phi(X)={Q,X}/2-K(X), and traceNorm(X-Phi(X)) at most min(2,10 delta) traceNorm(X). The ordinary trace of Phi(X) equals that of X, and positivity of X implies positivity of both Phi(X) and K(X) at every reference. For every ambient test Y, Tr(K(X)Y)=Tr(X sum B adjoint Y B). Thus this actual adjoint sends I to Q, and the same Kraus witnesses provide complete positivity and trace preservation of Phi at every reference. No state or Hermiticity restriction is placed on X or Y.")),
                Paragraph(Text("The ambient matrix trace is the ordinary unnormalized trace; center pinching preserves it, giving the sum trace on the embedded direct-sum algebra. The proof never compares that norm to a dimension-weighted surrogate. The live blockwise ambient energy estimate bounds Q and the same K. The central scalars commute with legal X and are scalar at each projection edge; expansion cancels exactly their linear and quadratic cross terms after center pinching. The anticommutator and K give 10 delta on arbitrary complex inputs through trace-norm duality. The actual unital Hermitian family and complete pinching give the independent channel contraction used for the cap 2. Transfers between distinct centers remain in both Q and K.")),
                Paragraph(Text("This proves the conditional global inference in original C109 equations 86.3 through 86.5 and its complete-reference min(2,10 delta) estimate. The source is AURIC_COMPOSITE_COMPARISON_FINITE_WITNESSES_COMMON_QUANTUM_SCALE_V96, Theorem 86.1 proof. The same actual S/H family, support and pseudoinverse normalization, Hermitian Kraus construction, Hilbert-Schmidt spectral bridge and variance premise with delta=beta, and final actual filter and whole-family normalization remain separate open obligations. The original full Theorem 86.1 is not claimed complete. No independent mathematical novelty is assigned to the pinching, trace duality or central cancellation helpers."))),
            DescribeRole.Theorem)
)));

    private static Formula DefectStatement()
    {
        var x=F.Id("x"); var e=F.Id("e"); var j=F.Id("j"); var n=F.Id("n");
        var h=F.Id("h"); var hj=At(h,j); var d=Delta;
        Formula Mean(Formula z) => RealPart(Inner(z,App(hj,z)));
        var variance=All("x",F.Id("E"),Implies(Unit(x),Leq(
            Sum("j",F.Id("J"),Sq(Norm(Sub(App(hj,x),Mul(Mean(x),x))))),d)));
        var assumptions=And(All("j",F.Id("J"),Call("IsSymmetric",hj)),
            And(Eqn(Sum("j",F.Id("J"),Mul(hj,hj)),Call("Id",F.Id("E"))),
                And(Leq(D(0),d),And(variance,Implies(ExistsUnit(),Unit(e))))));
        var re=Call("Ltwo",Call("Fin",n),F.Id("E"));
        var a=Call("Fin",Call("FiniteRank",re));
        var mat=Call("Matrix",a,a,ComplexType());
        var hjm=At(F.Id("H"),j); var mj=At(F.Id("M"),j); var q=F.Id("Q"); var xx=F.Id("X");
        var defH=All("j",F.Id("J"),Eqn(hjm,
            Call("MatrixOf",Call("stdBasis",re),Call("stdBasis",re),Call("Ref",n,hj))));
        var defM=All("j",F.Id("J"),Eqn(mj,Sub(hjm,Mul(Mean(e),Call("Id",a)))));
        var defQ=Eqn(q,Sum("j",F.Id("J"),Mul(Adj(mj),mj)));
        var defect=Sub(xx,Sum("j",F.Id("J"),Mul(hjm,Mul(xx,Adj(hjm)))));
        var identity=Eqn(defect,Sub(Mul(Frac(D(1),D(2)),
            Seq(Open,Mul(q,xx),Sp,Plus,Sp,Mul(xx,q),Close)),
            Sum("j",F.Id("J"),Mul(mj,Mul(xx,Adj(mj))))));
        var conclusion=All("n",Seq(Mathbb,Grp(F.Id("N"))),
            All("H",Call("Family",F.Id("J"),mat),
            All("M",Call("Family",F.Id("J"),mat),All("Q",mat,
                Implies(And(defH,And(defM,defQ)),All("X",mat,
                    And(identity,Leq(Call("traceNorm",defect),
                        Mul(Mul(D(1,0),d),Call("traceNorm",xx))))))))));
        return All("E",F.Id("Type"),All("J",F.Id("Type"),
            Seq(Instances("E"),Comma,Sp,OpenBracket,Call("Fintype",F.Id("J")),CloseBracket,
                Comma,Sp,All("h",Call("Family",F.Id("J"),
                    Call("LinearMap",ComplexType(),F.Id("E"),F.Id("E"))),
                    Seq(Forall,Sp,d,Colon,Sp,RealType(),Comma,Sp,
                        All("e",F.Id("E"),Implies(assumptions,conclusion)))))));
    }

    private static Formula Statement()
    {
        var e=F.Id("e"); var x=F.Id("x"); var j=F.Id("j"); var h=F.Id("h");
        var v=F.Id("V"); var n=F.Id("n"); var d=Delta;
        Formula Mean(Formula z) => RealPart(Inner(App(v,z),App(At(h,j),App(v,z))));
        var variance=All("x",F.Id("E"),Implies(Unit(x),Leq(
            Sum("j",F.Id("J"),Sq(Norm(Sub(App(At(h,j),App(v,x)),Mul(Mean(x),App(v,x)))))),d)));
        var assumptions=And(All("j",F.Id("J"),Call("IsSymmetric",At(h,j))),
            And(Leq(D(0),d),And(variance,Implies(ExistsUnit(),Unit(e)))));
        var cj=At(F.Id("c"),j); var lj=At(F.Id("L"),j); var mj=At(F.Id("M"),j);
        var re=Call("Ltwo",Call("Fin",n),F.Id("E"));
        var rf=Call("Ltwo",Call("Fin",n),F.Id("F"));
        var a=Call("Fin",Call("FiniteRank",re)); var b=Call("Fin",Call("FiniteRank",rf));
        var vb=Call("stdBasis",re); var wb=Call("stdBasis",rf);
        var definition=And(All("j",F.Id("J"),Eqn(cj,Mean(e))),
            All("j",F.Id("J"),Eqn(lj,Sub(Mul(At(h,j),v),Mul(cj,v)))));
        var matrixDefinition=All("j",F.Id("J"),Eqn(mj,Call("MatrixOf",vb,wb,Call("Ref",n,lj))));
        var result=All("n",Seq(Mathbb,Grp(F.Id("N"))),
            All("M",Call("Family",F.Id("J"),Call("Matrix",b,a,ComplexType())),Implies(matrixDefinition,
                All("X",Call("Matrix",a,a,ComplexType()),Leq(
                    Call("traceNorm",Sum("j",F.Id("J"),Mul(mj,Mul(F.Id("X"),Adj(mj))))),
                    Mul(Mul(D(5),d),Call("traceNorm",F.Id("X"))))))));
        var conclusion=All("c",Call("Family",F.Id("J"),RealType()),
            All("L",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("E"),F.Id("F"))),
                Implies(definition,result)));
        var body=All("V",Call("LinearIsometry",ComplexType(),F.Id("E"),F.Id("F")),
            All("h",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("F"),F.Id("F"))),
                Seq(Forall,Sp,d,Colon,Sp,RealType(),Comma,Sp,All("e",F.Id("E"),Implies(assumptions,conclusion)))));
        return All("E",F.Id("Type"),All("F",F.Id("Type"),All("J",F.Id("Type"),
            Seq(Instances("E"),Comma,Sp,Instances("F"),Comma,Sp,
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

    private static Formula GlobalStatement()
    {
        var i=F.Id("i"); var j=F.Id("j"); var t=F.Id("t"); var n=F.Id("n");
        var hspace=Call("Ltwo",F.Id("I"),F.Id("E"));
        var u=Call("Ltwo",Call("Fin",n),hspace); var rank=Call("Fin",Call("FiniteRank",u));
        var mat=Call("Matrix",rank,rank,ComplexType()); var vb=Call("stdBasis",u);
        var tt=Call("Product",F.Id("J"),F.Id("I"),F.Id("I"));
        var p=F.Id("P"); var hj=At(F.Id("H"),j); var mj=At(F.Id("M"),j); var q=F.Id("Q");
        var at=At(F.Id("A"),t); var bt=At(F.Id("B"),t); var x=F.Id("X"); var y=F.Id("Y");
        var tj=Call("first",t); var ti=Call("secondfirst",t); var tk=Call("secondsecond",t);
        Formula Pinch(Formula z)=>Call("centerPinching",p,z);
        Formula MatrixOf(Formula z)=>Call("MatrixOf",vb,vb,Call("Ref",n,z));
        Formula Pi(Formula z)=>At(p,z);
        var definitions=Conj(
            All("i",F.Id("I"),Eqn(Pi(i),MatrixOf(Call("blockProjection",F.Id("E"),i)))),
            All("j",F.Id("J"),Eqn(hj,MatrixOf(At(F.Id("h"),j)))),
            All("j",F.Id("J"),Eqn(mj,MatrixOf(Sub(At(F.Id("h"),j),Call("centralMean",F.Id("h"),F.Id("e"),j))))),
            Eqn(q,Pinch(Sum("j",F.Id("J"),Mul(mj,mj)))),
            All("t",tt,Eqn(at,Mul(Pi(tk),Mul(At(F.Id("H"),tj),Pi(ti))))),
            All("t",tt,Eqn(bt,Mul(Pi(tk),Mul(At(F.Id("M"),tj),Pi(ti))))));
        var k=Pinch(Sum("j",F.Id("J"),Mul(mj,Mul(x,mj))));
        var phi=Pinch(Sum("j",F.Id("J"),Mul(hj,Mul(x,hj))));
        var legal=All("i",F.Id("I"),Eqn(Mul(Pi(i),x),Mul(x,Pi(i))));
        var identity=Eqn(Sub(x,phi),Sub(Mul(Frac(D(1),D(2)),
            Seq(Open,Mul(q,x),Sp,Plus,Sp,Mul(x,q),Close)),k));
        var bounds=Leq(Call("traceNorm",Sub(x,phi)),
            Mul(Call("min",D(2),Mul(D(1,0),Delta)),Call("traceNorm",x)));
        var pairing=All("Y",mat,Eqn(Call("Tr",Mul(k,y)),
            Call("Tr",Mul(x,Sum("t",tt,Mul(Adj(bt),Mul(y,bt)))))));
        var input=All("X",mat,Implies(legal,Conj(
            Eqn(k,Sum("t",tt,Mul(bt,Mul(x,Adj(bt))))),
            Eqn(phi,Sum("t",tt,Mul(at,Mul(x,Adj(at))))),identity,bounds,
            Eqn(Call("Tr",phi),Call("Tr",x)),Implies(Leq(D(0),x),Leq(D(0),phi)),
            Implies(Leq(D(0),x),Leq(D(0),k)),pairing)));
        var conclusions=Conj(Leq(q,Mul(Mul(D(5),Delta),Call("Id",rank))),
            Eqn(Sum("t",tt,Mul(Adj(at),at)),Call("Id",rank)),
            Eqn(Sum("t",tt,Mul(Adj(bt),bt)),q),
            All("Y",mat,Eqn(Call("Tr",Pinch(y)),Call("Tr",y))),
            All("Y",mat,All("i",F.Id("I"),Eqn(Mul(Pi(i),Pinch(y)),Mul(Pinch(y),Pi(i))))),input);
        var refResult=All("n",Seq(Mathbb,Grp(F.Id("N"))),Quantify(Implies(definitions,conclusions),
            ("P",Call("Family",F.Id("I"),mat)),("H",Call("Family",F.Id("J"),mat)),
            ("M",Call("Family",F.Id("J"),mat)),("Q",mat),
            ("A",Call("Family",tt,mat)),("B",Call("Family",tt,mat))));
        return DirectSumBinders(Seq(Forall,Sp,Delta,Colon,Sp,RealType(),Comma,Sp,Quantify(Implies(DirectSumAssumptions(true),refResult),
            ("h",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),hspace,hspace))),
            ("e",Call("Sections",F.Id("E"))))));
    }

    private static Formula Instances(string x) => Seq(
        OpenBracket,Call("NormedAddCommGroup",F.Id(x)),CloseBracket,Sp,
        OpenBracket,Call("InnerProductSpace",ComplexType(),F.Id(x)),CloseBracket,Sp,
        OpenBracket,Call("FiniteDimensional",ComplexType(),F.Id(x)),CloseBracket);
    private static Formula ExistsUnit() => Seq(Open,Exists,Sp,F.Id("x"),Colon,Sp,F.Id("E"),Comma,Sp,Unit(F.Id("x")),Close);
    private static Formula Frac(Formula a,Formula b) => new Formula.Fraction(a,b);
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
