using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class HSPowerProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HSPowerProduct", H("HSPowerProduct"), Blocks(
            Describe.Lean(DescribeId.Create("perspective-lr-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSPowerProduct.perspective_lr_eq"),
                H("Full HS perspective identity"), StatementSource.FromAuthor(Perspective()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(Paragraph(Text("On a finite nontrivial complex Hilbert space and for every real s, the perspective of leftMulHS A and rightMulHS B equals leftMulHS(A^s) rightMulHS(B^(1-s)). The public arbitrary-K scalar bridge is applied with K=V adjoint for every HS vector V. Selfadjointness and complex polarization convert equality of real quadratic forms to operator equality. This supplies the product powers used by the common-right-factor mean."))), DescribeRole.Theorem),
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
}
