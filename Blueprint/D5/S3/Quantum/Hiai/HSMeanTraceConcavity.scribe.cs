using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class HSMeanTraceConcavityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HSMeanTraceConcavity", H("HSMeanTraceConcavity"), Blocks(
            Describe.Lean(DescribeId.Create("meanproduct-triple-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSMeanTraceConcavity.meanProduct_triple_concave"),
                H("Triple operator concavity"), StatementSource.FromAuthor(Triple(false,false)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For p and theta in [0,1], form P_p(X,W)=L_(X^p) R_(W^(1-p)). Its joint operator concavity follows from the public full HS perspective identity and all-Hilbert power-perspective concavity. Mix A, B and W with one common coefficient. Both-input mean monotonicity compares the endpoint mixtures with the two Lieb lifts at the mixture; joint mean concavity then yields the triple operator inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gamma-triple-concave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSMeanTraceConcavity.gamma_triple_concave"),
                H("Triple trace concavity"), StatementSource.FromAuthor(Triple(false,true)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For arbitrary fixed Z, Gamma(A,B,W)=Re Tr(Z adjoint (B^p #theta A^p) Z W^(1-p)) is jointly concave in all three strictly positive inputs, for p and theta in [0,1]. The common-right-factor identity identifies the HS geometric mean. Evaluation at the fixed HS vector Z preserves the operator inequality. No positivity is asserted for the nonsymmetric product inside the trace, and Z may be singular or zero. This is the joint auxiliary-variable inequality required for endpoint-optimizer interpolation."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.")))));

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
}
