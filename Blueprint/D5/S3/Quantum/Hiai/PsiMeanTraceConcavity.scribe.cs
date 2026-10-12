using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class PsiMeanTraceConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Hiai mean-trace concavity through the Hilbert-Schmidt lift and forward trace Young.",
        H("PsiMeanTraceConcavity"), Blocks(
Describe.Lean(DescribeId.Create("perspective-lr-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.perspective_lr_eq"),
                H("Full HS perspective identity"), StatementSource.FromAuthor(Perspective()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(Paragraph(Text("On a finite nontrivial complex Hilbert space and for every real s, the perspective of leftMulHS A and rightMulHS B equals leftMulHS(A^s) rightMulHS(B^(1-s)). The public arbitrary-K scalar bridge is applied with K=V adjoint for every HS vector V. Selfadjointness and complex polarization convert equality of real quadratic forms to operator equality. This supplies the product powers used by the common-right-factor mean."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lr-pd"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.lr_pd"),
                H("Strict positivity of the action product"), StatementSource.FromAuthor(ProductPositive()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("The product of left multiplication by strictly positive X and right multiplication by strictly positive D is strictly positive on the true HS space. Left and right actions commute, even when the original operators do not."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lr-power"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.lr_power"),
                H("All real powers of the HS product"), StatementSource.FromAuthor(ProductPower()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real s, (L_X R_D)^s = L_(X^s) R_(D^s) on finite nontrivial complex Hilbert space. The full public perspective identity gives the normalized power after cancellation of the invertible right square-root sandwich. Substituting the inverse of D recovers arbitrary powers. Right multiplication reverses products, and every combined right factor here is a power of this same D."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-lr-common"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.mean_lr_common"),
                H("Common right factor in the genuine mean"), StatementSource.FromAuthor(CommonMean()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real theta, the genuine mean of L_X R_D and L_Y R_D is L_(X #theta Y) R_D. In the normalized middle the right factors D^(-1/2), D, D^(-1/2) cancel; the outer two D^(1/2) factors multiply to D. X and Y may be noncommuting. The triple-variable concavity theorem uses this exact identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("meanproduct-triple-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.meanProduct_triple_concave"),
                H("Triple operator concavity"), StatementSource.FromAuthor(Triple(false,false)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For p and theta in [0,1], form P_p(X,W)=L_(X^p) R_(W^(1-p)). Its joint operator concavity follows from the public full HS perspective identity and all-Hilbert power-perspective concavity. Mix A, B and W with one common coefficient. Both-input mean monotonicity compares the endpoint mixtures with the two Lieb lifts at the mixture; joint mean concavity then yields the triple operator inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hs-gamma-triple-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.hs_gamma_triple_concave"),
                H("Triple trace concavity"), StatementSource.FromAuthor(Triple(false,true)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For arbitrary fixed Z, Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in all three strictly positive inputs, for p and theta in [0,1]. The common-right-factor identity identifies the HS geometric mean. Evaluation at the fixed HS vector Z preserves the operator inequality. No positivity is asserted for the nonsymmetric product inside the trace, and Z may be singular or zero. This is the joint auxiliary-variable inequality required for endpoint-optimizer interpolation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("forward-trace-young"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.forward_trace_young"),
                H("Forward tracial Young inequality"), StatementSource.FromAuthor(Young()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("For all finite complex matrix dimensions, positive definite M and W and 0<p<=1, Re Tr(M W^(1-p))-(1-p) Re Tr W <= p Re Tr(M^(1/p)). For 0<p<1, apply the existing Schatten Holder supplier to M^(1/2) W^((1-p)/2) at exponents 2, 2/p and 2/(1-p). The public column-Gram identity and trace cyclicity give the mixed trace. Raising the bound to two and applying scalar weighted Young proves the result. The endpoint p=1 is calculated separately. Empty dimension and noncommuting M,W are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximum-and-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.maximum_and_attainment"),
                H("Explicit attained maximum"), StatementSource.FromAuthor(Maximum()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("An explicit positive definite maximizer is W0=M^(1/p), and the objective equals p Re Tr(M^(1/p)) there and dominates its value at every positive definite W. At p=1 the objective is independent of W, so uniqueness is not asserted. The equality uses same-matrix spectral power arithmetic. No positive definite optimizer is asserted for singular M. The mean-trace concavity proof interpolates the two actual endpoint optimizers; it needs joint concavity in the auxiliary variable, not a supremum of separately concave functions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-gamma-triple-concavity"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.gamma_triple_concave"),
                H("Joint concavity in three matrix inputs"), StatementSource.FromAuthor(Triple(true,true)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every finite complex matrix dimension, arbitrary fixed Z, p and theta in [0,1], the real trace pairing Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in the three positive definite inputs. All mixtures use one common coefficient. The spectral matrix mean is transported to the genuine Hilbert-Schmidt mean through the public matrix/operator star-algebra equivalence. Generic continuous functional calculus preserves spectral powers, and the public trace-to-matrix identity preserves the real trace. Empty dimension is split explicitly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-psi-joint-concavity"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/PsiMeanTraceConcavity.psi_jointly_concave"),
                H("Exact mean-trace concavity"), StatementSource.FromAuthor(PsiConcavity()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every finite complex matrix dimension, 0<p<=1, theta in [0,1] and fixed invertible complex Z, Psi(A,B)=Re Tr((Z adjoint (B^p #theta A^p) Z)^(1/p)) is jointly concave on all positive definite A,B. They may be noncommuting, and Z need not be selfadjoint. The genuine mean convention is X #theta Y=X^(1/2)(X^(-1/2) Y X^(-1/2))^theta X^(1/2). Thus B^p is the base. All powers are the actual spectral CFC powers; the outer reciprocal power is inside the trace.")),
                    Paragraph(Text("Invertibility of Z makes each mean congruence positive definite. The forward trace-Young maximum is attained at W=M^(1/p). Choose these two endpoint optimizers, mix them within the positive definite cone, and apply triple joint concavity to Gamma minus its affine trace penalty. The universal Young bound at the mixture then gives p times Psi(mixture) >= p times the mixture of the two endpoint values. Division by p>0 concludes the proof. An arbitrary supremum of separately concave functions is not used. The p=1 and theta=0,1 endpoints are retained by the suppliers, and the matrix triple theorem treats empty dimension separately.")),
                    Paragraph(Text("This is the classical Hiai Lemma 3.3 target, obtained by a connected Hilbert-Schmidt and tracial variational derivation. It does not settle the full open Problem 5.18 of arXiv:2510.04691v3. That problem still requires inverse-geometric identification, its original variational parameter assembly, and a source-faithful common-epsilon-I limit preserving s(A)>=s(B). No positive definite optimizer is claimed for singular M or noninvertible Z. Compilation is not an official acceptance claim."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Id(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(Id("C")));
    private static Formula Op => Call("L", Id("H"));
    private static Formula Bind(Formula type, string[] names, Formula body)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(Id(names[i]));
        }
        items.AddRange([Colon, Sp, type, Comma, Esc, body]);
        return Seq([.. items]);
    }
    private static Formula And(params Formula[] facts)
    {
        var items = new List<Formula>();
        for (var i = 0; i < facts.Length; i++)
        {
            if (i > 0) items.AddRange([Land, Sp]);
            items.Add(facts[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Imp(Formula hypothesis, Formula conclusion) =>
        Seq(hypothesis, Implies, Esc, conclusion);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Pd(Formula x) => Call("pdSet", x);
    private static Formula Pow(Formula x, Formula s) => Call("rpow", x, s);
    private static Formula OneMinus(Formula t) => Seq(Open, D(1), Minus, t, Close);
    private static Formula Hilbert(Formula body, bool finite = false)
    {
        var h = Id("H");
        var items = new List<Formula>();
        foreach (var instance in new[] { Call("NormedAddCommGroup", h),
            Call("InnerProductSpace", Complex, h), Call("CompleteSpace", h), Call("Nontrivial", h) })
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        if (finite) items.AddRange([OpenBracket, Call("FiniteDimensional", Complex, h),
            CloseBracket, Comma, Sp]);
        items.Add(body);
        return Bind(Call("Level"), ["u"], Bind(Call("Type", Id("u")), ["H"], Seq([.. items])));
    }
    private static Formula Perspective()
    {
        var s=Id("s"); var a=Id("A"); var b=Id("B");
        return Hilbert(Bind(Real,["s"],Bind(Op,["A","B"],
            Imp(And(Pd(a),Pd(b)),Eqn(
                Call("operatorPowerMean",s,D(1),Call("leftMulHS",a),Call("rightMulHS",b)),
                Seq(Call("leftMulHS",Pow(a,s)),Call("rightMulHS",Pow(b,OneMinus(s)))))))),true);
    }
    private static Formula Lr(Formula x, Formula d) => Call("lr",x,d);
    private static Formula ProductPositive()
    {
        var x=Id("X"); var d=Id("D");
        return Hilbert(Bind(Op,["X","D"],Imp(And(Pd(x),Pd(d)),Pd(Lr(x,d)))),true);
    }
    private static Formula ProductPower()
    {
        var s=Id("s"); var x=Id("X"); var d=Id("D");
        return Hilbert(Bind(Real,["s"],Bind(Op,["X","D"],
            Imp(And(Pd(x),Pd(d)),Eqn(Pow(Lr(x,d),s),Lr(Pow(x,s),Pow(d,s)))))),true);
    }
    private static Formula CommonMean()
    {
        var theta=Id("theta"); var x=Id("X"); var y=Id("Y"); var d=Id("D");
        return Hilbert(Bind(Real,["theta"],Bind(Op,["X","Y","D"],
            Imp(And(Pd(x),Pd(y),Pd(d)),Eqn(Call("mean",theta,Lr(x,d),Lr(y,d)),
                Lr(Call("mean",theta,x,y),d))))),true);
    }
    private static Formula Mat => Call("Matrix", Id("d"), Id("d"), Complex);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Le, Sp, y);
    private static Formula UnitInterval(Formula x) => And(Leq(D(0), x), Leq(x, D(1)));
    private static Formula Pos(Formula x) => Call("PosDef", x);
    private static Formula Scale(Formula t, Formula x) => Call("smul", t, x);
    private static Formula Mix(Formula t, Formula x, Formula y) =>
        Seq(Scale(OneMinus(t), x), Plus, Scale(t, y));
    private static Formula MatrixScope(Formula body) =>
        Bind(Call("Level"), ["u"], Bind(Call("Type", Id("u")), ["d"],
            Seq(OpenBracket, Call("Fintype", Id("d")), CloseBracket, Comma, Sp,
                OpenBracket, Call("DecidableEq", Id("d")), CloseBracket, Comma, Esc, body)));
    private static Formula Triple(bool matrix, bool trace)
    {
        var p=Id("p"); var theta=Id("theta"); var t=Id("t"); var z=Id("Z");
        var az=Id("Az"); var ao=Id("Ao"); var bz=Id("Bz"); var bo=Id("Bo");
        var wz=Id("Wz"); var wo=Id("Wo");
        Formula PD(Formula x) => matrix ? Pos(x) : Pd(x);
        Formula Value(Formula a,Formula b,Formula w) => trace ? Call("gamma",p,theta,z,a,b,w) :
            Call("mean",theta,Call("powerProduct",p,b,w),Call("powerProduct",p,a,w));
        var left = trace ? Seq(OneMinus(t),Value(az,bz,wz),Plus,t,Value(ao,bo,wo)) :
            Seq(Scale(OneMinus(t),Value(az,bz,wz)),Plus,Scale(t,Value(ao,bo,wo)));
        var statement=Imp(And(UnitInterval(p),UnitInterval(theta),PD(az),PD(ao),PD(bz),PD(bo),
            PD(wz),PD(wo),UnitInterval(t)),Leq(left,Value(Mix(t,az,ao),Mix(t,bz,bo),Mix(t,wz,wo))));
        var body=Bind(matrix ? Mat : Op,["Az","Ao","Bz","Bo","Wz","Wo"],statement);
        if(trace) body=Bind(matrix ? Mat : Op,["Z"],body);
        body=Bind(Real,["p","theta","t"],body);
        return matrix ? MatrixScope(body) : Hilbert(body,true);
    }
    private static Formula Objective(Formula p,Formula m,Formula w) => Call("objective",p,m,w);
    private static Formula Bound(Formula p,Formula m) =>
        Seq(p,Call("tracePower",new Formula.Fraction(D(1),p),m));
    private static Formula Young()
    {
        var p=Id("p"); var m=Id("M"); var w=Id("W");
        return MatrixScope(Bind(Real,["p"],Bind(Mat,["M","W"],
            Imp(And(Pos(m),Pos(w),Seq(D(0),Lt,p),Leq(p,D(1))),Leq(Objective(p,m,w),Bound(p,m))))));
    }
    private static Formula Maximum()
    {
        var p=Id("p"); var m=Id("M"); var w=Id("W"); var v=Id("V");
        return MatrixScope(Bind(Real,["p"],Bind(Mat,["M"],
            Imp(And(Pos(m),Seq(D(0),Lt,p),Leq(p,D(1))),
                Seq(Exists,Sp,w,Colon,Sp,Mat,Comma,Esc,And(Pos(w),
                    Eqn(w,Pow(m,new Formula.Fraction(D(1),p))),
                    Eqn(Objective(p,m,w),Bound(p,m)),
                    Seq(Open,Bind(Mat,["V"],Imp(Pos(v),Leq(Objective(p,m,v),Objective(p,m,w)))),Close)))))));
    }
    private static Formula PsiConcavity()
    {
        var p=Id("p"); var theta=Id("theta"); var z=Id("Z"); var a=Id("A"); var b=Id("B");
        return MatrixScope(Bind(Real,["p","theta"],Bind(Mat,["Z"],
            Imp(And(Seq(D(0),Lt,p),Leq(p,D(1)),UnitInterval(theta),Call("IsUnit",z)),
                Call("JointlyConcaveOn",Call("PosDefCone",Mat),Call("PosDefCone",Mat),
                    Seq(LambdaLower,Sp,a,Comma,Sp,b,Mapsto,Sp,Call("psi",p,theta,z,a,b)))))));
    }
}
