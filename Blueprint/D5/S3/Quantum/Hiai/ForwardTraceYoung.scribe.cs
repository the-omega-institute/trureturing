using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class ForwardTraceYoungDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ForwardTraceYoung", H("ForwardTraceYoung"), Blocks(
            Describe.Lean(DescribeId.Create("forward-trace-young"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ForwardTraceYoung.forward_trace_young"),
                H("Forward tracial Young inequality"), StatementSource.FromAuthor(Young()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("For all finite complex matrix dimensions, positive definite M and W and 0<p<=1, Re Tr(M W^(1-p))-(1-p) Re Tr W <= p Re Tr(M^(1/p)). For 0<p<1, apply the existing Schatten Holder supplier to M^(1/2) W^((1-p)/2) at exponents 2, 2/p and 2/(1-p). The public column-Gram identity and trace cyclicity give the mixed trace. Raising the bound to two and applying scalar weighted Young proves the result. The endpoint p=1 is calculated separately. Empty dimension and noncommuting M,W are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximum-and-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/ForwardTraceYoung.maximum_and_attainment"),
                H("Explicit attained maximum"), StatementSource.FromAuthor(Maximum()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/carlenlieb2008minkowski")),
                Blocks(Paragraph(Text("The positive definite optimizer is exactly W0=M^(1/p), and the objective equals p Re Tr(M^(1/p)) there and dominates its value at every positive definite W. The equality uses same-matrix spectral power arithmetic. No positive definite optimizer is asserted for singular M. The mean-trace concavity proof interpolates the two actual endpoint optimizers; it needs joint concavity in the auxiliary variable, not a supremum of separately concave functions."))), DescribeRole.Theorem),
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
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Le, Sp, y);
    private static Formula Pos(Formula x) => Call("PosDef", x);
    private static Formula Pow(Formula x, Formula s) => Call("rpow", x, s);
    private static Formula MatrixScope(Formula body) =>
        Bind(Call("Level"), ["u"], Bind(Call("Type", Id("u")), ["d"],
            Seq(OpenBracket, Call("Fintype", Id("d")), CloseBracket, Comma, Sp,
                OpenBracket, Call("DecidableEq", Id("d")), CloseBracket, Comma, Esc, body)));

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
}
