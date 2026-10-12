using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class PsiMeanTraceConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hiai mean-trace concavity", H("PsiMeanTraceConcavity"), Blocks(
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
                    Paragraph(Text("This is the classical Hiai Lemma 3.3 target, obtained by a connected Hilbert-Schmidt and tracial variational derivation. It does not settle the full open Problem 5.18 of arXiv:2510.04691v3. That problem still requires inverse-geometric identification, its original variational parameter assembly, and a source-faithful common-epsilon-I limit preserving s(A)>=s(B). No positive definite optimizer is claimed for singular M or noninvertible Z. The native four-slot escape audit remains unfinished under issue #5214; compilation is not declared_validated registration or official acceptance."))), DescribeRole.Theorem))));

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
    private static Formula Mat => Call("Matrix", Id("d"), Id("d"), Complex);
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
    private static Formula Leq(Formula x, Formula y) => Seq(x, Le, Sp, y);
    private static Formula UnitInterval(Formula x) => And(Leq(D(0), x), Leq(x, D(1)));
    private static Formula Pd(Formula x) => Call("pdSet", x);
    private static Formula Pos(Formula x) => Call("PosDef", x);
    private static Formula OneMinus(Formula t) => Seq(Open, D(1), Minus, t, Close);
    private static Formula Scale(Formula t, Formula x) => Call("smul", t, x);
    private static Formula Mix(Formula t, Formula x, Formula y) =>
        Seq(Scale(OneMinus(t), x), Plus, Scale(t, y));
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

    private static Formula PsiConcavity()
    {
        var p=Id("p"); var theta=Id("theta"); var z=Id("Z"); var a=Id("A"); var b=Id("B");
        return MatrixScope(Bind(Real,["p","theta"],Bind(Mat,["Z"],
            Imp(And(Seq(D(0),Lt,p),Leq(p,D(1)),UnitInterval(theta),Call("IsUnit",z)),
                Call("JointlyConcaveOn",Call("PosDefCone",Mat),Call("PosDefCone",Mat),
                    Seq(LambdaLower,Sp,a,Comma,Sp,b,Mapsto,Sp,Call("psi",p,theta,z,a,b)))))));
    }
}
