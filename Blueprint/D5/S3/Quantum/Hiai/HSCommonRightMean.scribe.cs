using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class HSCommonRightMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HSCommonRightMean", H("HSCommonRightMean"), Blocks(
            Describe.Lean(DescribeId.Create("lr-pd"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSCommonRightMean.lr_pd"),
                H("Strict positivity of the action product"), StatementSource.FromAuthor(ProductPositive()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("The product of left multiplication by strictly positive X and right multiplication by strictly positive D is strictly positive on the true HS space. Left and right actions commute, even when the original operators do not."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lr-power"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSCommonRightMean.lr_power"),
                H("All real powers of the HS product"), StatementSource.FromAuthor(ProductPower()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real s, (L_X R_D)^s = L_(X^s) R_(D^s) on finite nontrivial complex Hilbert space. The full public perspective identity gives the normalized power after cancellation of the invertible right square-root sandwich. Substituting the inverse of D recovers arbitrary powers. Right multiplication reverses products, and every combined right factor here is a power of this same D."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-lr-common"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/HSCommonRightMean.mean_lr_common"),
                H("Common right factor in the genuine mean"), StatementSource.FromAuthor(CommonMean()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every real theta, the genuine mean of L_X R_D and L_Y R_D is L_(X #theta Y) R_D. In the normalized middle the right factors D^(-1/2), D, D^(-1/2) cancel; the outer two D^(1/2) factors multiply to D. X and Y may be noncommuting. The triple-variable concavity theorem uses this exact identity."))), DescribeRole.Theorem),
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
}
