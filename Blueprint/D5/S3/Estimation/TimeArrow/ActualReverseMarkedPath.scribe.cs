using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class ActualReverseMarkedPathDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Transpose Kernel Marked Counts", H("Actual Transpose Kernel Marked Counts"), Blocks(
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reverseprobability"), DeclarationHandle.Create(Module + "reverseProbability"),
            H("reverseProbability"), StatementSource.FromAuthor(Disp(Q("M q s", V("Nat"), Q("r", V("Real"), Q("S", SupportF, Q("e", Call("Experiment"), Q("o", Call("Obs", V("M"), V("s"), V("e")), Eqn(Call("reverseProbability", V("r"), V("e"), V("S"), V("o")), Call("transposeHistoryMass", V("M"), V("r"), V("e"), V("S"), V("o")))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For pairs, transposeHistoryMass is the product over s ordered pairs (x,y) of (2M)^(-1) transition(r,S,y,x). For a path it is (2M)^(-1) times the product of transition(r,S,X(t+1),X(t)). The support S is fixed for the entire history."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reversepgf"), DeclarationHandle.Create(Module + "reversePGF"),
            H("reversePGF"), StatementSource.FromAuthor(Disp(Native(Q("zp zm", Tilts, Q("e", Call("Experiment"), Eqn(Call("reversePGF", V("r"), V("S"), V("m"), V("zp"), V("zm"), V("s"), V("e")), Call("reverseCountMonomialSum", V("r"), V("S"), V("m"), V("zp"), V("zm"), V("s"), V("e")))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The right side sums reverseProbability times the product over marked rows j of zp(j)^count(e,o,m(j),1) zm(j)^count(e,o,m(j),-1), over all complete histories o of the chosen experiment."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reversea"), DeclarationHandle.Create(Module + "reverseA"),
            H("reverseA"), StatementSource.FromAuthor(Disp(Q("M k", V("Nat"), Q("zp zm", Tilts, Eqn(Call("reverseA", V("M"), V("zp"), V("zm")), DivF(Call("sumSymmetricTilt", V("zp"), V("zm")), Mul(N(2), V("M")))))) )), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A is the sum of u(j)/(2M), where u(j)=(zp(j)+zm(j))/2-1. The reverse one-edge marked means are s/(4M)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reverseg"), DeclarationHandle.Create(Module + "reverseG"),
            H("reverseG"), StatementSource.FromAuthor(Disp(Q("M k", V("Nat"), Q("zp zm", Tilts, Eqn(Call("reverseG", V("M"), V("zp"), V("zm")), DivF(Call("sumAntisymmetricTilt", V("zp"), V("zm")), Mul(N(2), V("M")))))) )), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("G is the sum of v(j)/(2M), where v(j)=(zp(j)-zm(j))/2."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reversed"), DeclarationHandle.Create(Module + "reverseD"),
            H("reverseD"), StatementSource.FromAuthor(Disp(Native(Q("zp zm", Tilts, Eqn(Call("reverseD", V("r"), V("S"), V("m"), V("zp"), V("zm")), Call("symmetricProfileAverage", V("M"), V("r"), V("S"), V("m"), V("zp"), V("zm")))), "M q k"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The symmetricProfileAverage is (2M)^(-1) times the sum of b(r,S,inl(m(j))) times the u(j) tilt. Marks can lie in signal or background rows."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reversee"), DeclarationHandle.Create(Module + "reverseE"),
            H("reverseE"), StatementSource.FromAuthor(Disp(Native(Q("zp zm", Tilts, Eqn(Call("reverseE", V("r"), V("S"), V("m"), V("zp"), V("zm")), Call("antisymmetricProfileAverage", V("M"), V("r"), V("S"), V("m"), V("zp"), V("zm")))), "M q k"))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The antisymmetricProfileAverage is (2M)^(-1) times the sum of b(r,S,inl(m(j))) times the v(j) tilt. Marks can lie in signal or background rows."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reversematrix"), DeclarationHandle.Create(Module + "reverseMatrix"),
            H("reverseMatrix"), StatementSource.FromAuthor(Disp(Q("A G D E", V("Complex"), Eqn(Call("reverseMatrix", V("A"), V("G"), V("D"), V("E")), MatrixF())))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The nine matrix entries are in row order. At zero drift the lower two coordinates form a length-two nilpotent block."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-reversestate"), DeclarationHandle.Create(Module + "reverseState"),
            H("reverseState"), StatementSource.FromAuthor(Disp(Q("A G D E", V("Complex"), AndF(Eqn(Call("reverseState", V("A"), V("G"), V("D"), V("E"), N(0)), Call("vector", N(1), N(0), N(0))), Q("t", V("Nat"), Eqn(Call("reverseState", V("A"), V("G"), V("D"), V("E"), Add(V("t"), N(1))), Call("rowTransfer", Call("reverseState", V("A"), V("G"), V("D"), V("E"), V("t")), MatrixF()))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The state is a row-coordinate vector initialized at (1,0,0); rowTransfer multiplies it by the displayed matrix. Its coordinates are the coefficients of the endpoint density (x+chi(y) ycoef+b(y) z)/(2M)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-actual-reverse-marked-path-pgf"), DeclarationHandle.Create(Module + "actual_reverse_marked_path_pgf"),
            H("actual reverse marked path pgf"), StatementSource.FromAuthor(Disp(Native(Imp(Hyp, Q("zp zm", Tilts, Eqn(Pgf("path"), Call("entry", Pow(DriftMatrix(), V("s")), N(0), N(0)))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every natural s, including s=0, the actual continuous transpose-kernel history PGF is the (0,0) entry of the s-th power of Cminus. The complex tilts are unrestricted, including zero. Cminus is reverseMatrix evaluated at A,G,D,E of the same support and marked rows."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-actual-reverse-marked-pair-pgf"), DeclarationHandle.Create(Module + "actual_reverse_marked_pair_pgf"),
            H("actual reverse marked pair pgf"), StatementSource.FromAuthor(Disp(Native(Imp(Hyp, Q("zp zm", Tilts, Eqn(Pgf("pair"), Pow(Add(N(1), Drift("reverseA")), V("s")))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For independent stationary adjacent pairs, the actual transpose kernel gives the single-pair PGF 1+A exactly, before the independent product is taken."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-actual-reverse-marked-poisson-envelope"), DeclarationHandle.Create(Module + "actual_reverse_marked_poisson_envelope"),
            H("actual reverse marked poisson envelope"), StatementSource.FromAuthor(Disp(Native(Imp(Hyp, Q("zp zm", Tilts, Q("e", Call("Experiment"), Q("eta", V("Real"), Imp(AndF(Le(N(0), V("eta")), Le(V("eta"), DivF(N(1), D(6,4))), Call("fourDriftBounds", V("M"), V("r"), V("S"), V("m"), V("zp"), V("zm"), V("eta")), Le(Mul(V("s"), Pow(V("eta"), N(2))), DivF(N(1), D(2,5,6)))), Le(Norm(SubF(Pgf("e"), Call("exp", Mul(V("s"), Drift("reverseA"))))), Mul(Mul(Mul(D(8,0), V("s")), Pow(V("eta"), N(2))), Call("exp", Mul(V("s"), Call("realPart", Drift("reverseA")))))))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("fourDriftBounds bounds the norms of A,G,D,E by eta. The estimate holds for the actual pair and path experiments, retaining the signed real exponential scale. Dividing the three-coordinate recurrence by exp(A)^t gives a transient norm 4 norm(y)+norm(z). Its contraction and the quadratic defect of exp(A) yield the bound uniformly on every polydisk on which the drift hypotheses hold."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("actualreversemarkedpath-actual-reverse-marked-count-relative"), DeclarationHandle.Create(Module + "actual_reverse_marked_count_relative"),
            H("actual reverse marked count relative"), StatementSource.FromAuthor(Disp(ReverseRelative())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Constants depend only on Czero. The scale L=s/(2M) is real; no divisibility is imposed on s. For M>=Mzero, 1<=q<M, 0<r<1, compensation<1, L>=1, L/M<=etazero, k=1 or 2, every fixed support, distinct marks and both experiments, P is the mass of the simultaneous count tuple and Q is the product of 2k Poisson masses at the exact mean L/2. Every prescribed coordinate is at most Czero L. The estimate includes all zero counts and rare point masses."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula N(byte n) => D(n);
    private static Formula Call(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula Q(string names, Formula type, Formula body) =>
        Seq(Forall, Sp, Seq([.. names.Split(' ').SelectMany((s, i) => i == 0 ? new[] { V(s) } : new[] { Comma, V(s) })]), Colon, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, type, Comma, Sp, body);
    private static Formula Fn(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula SubF(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, Open, b, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula DivF(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula AndF(params Formula[] xs) => Join(xs, Land);
    private static Formula Join(Formula[] xs, Formula op)
    {
        var p = new List<Formula>();
        for (var i = 0; i < xs.Length; i++) { if (i > 0) p.AddRange([Sp, op, Sp]); p.Add(xs[i]); }
        return Seq([.. p]);
    }
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula AbsF(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula FinF(Formula a) => Call("Fin", a);
    private static Formula SupportF => Call("Support", V("M"), V("q"));
    private static Formula Marks => Fn(FinF(V("k")), FinF(V("M")));
    private static Formula Tilts => Fn(FinF(V("k")), V("Complex"));
    private static Formula Native(Formula body, string naturals = "M q s k") => Q(naturals, V("Nat"), Q("r", V("Real"), Q("S", SupportF, Q("m", Marks, body))));
    private static Formula Hyp => AndF(Le(N(1), V("q")), LtF(V("q"), V("M")), LtF(N(0), V("r")), LtF(V("r"), N(1)), LtF(Call("compensation", V("M"), V("q"), V("r")), N(1)), Call("injective", V("m")));
    private static Formula SmallK => Seq(Open, V("k"), Eq, N(1), Sp, Lor, Sp, V("k"), Eq, N(2), Close);
    private static Formula L => DivF(V("s"), Mul(N(2), V("M")));
    private static Formula MatrixF() => Call("matrix", Add(N(1), V("A")), V("G"), Add(V("A"), V("G")), V("A"), V("G"), Add(Add(N(1), V("A")), V("G")), V("D"), V("E"), Add(V("D"), V("E")));
    private static Formula Drift(string name) => name is "reverseA" or "reverseG" ? Call(name, V("M"), V("zp"), V("zm")) : Call(name, V("r"), V("S"), V("m"), V("zp"), V("zm"));
    private static Formula DriftMatrix() => Call("reverseMatrix", Drift("reverseA"), Drift("reverseG"), Drift("reverseD"), Drift("reverseE"));
    private static Formula Pgf(string e) => Call("reversePGF", V("r"), V("S"), V("m"), V("zp"), V("zm"), V("s"), V(e));
    private static Formula ReverseRelative()
    {
        Formula result = Native(Imp(AndF(Hyp, Le(V("Mzero"), V("M")), Le(N(1), L), Le(DivF(L, V("M")), V("etazero")), SmallK),
            Q("np nm", Fn(FinF(V("k")), V("Nat")), Imp(Call("coordinateCountBound", V("np"), V("nm"), V("Czero"), L),
            Q("e", Call("Experiment"), Le(AbsF(SubF(DivF(Call("reversePointMass", V("r"), V("S"), V("m"), V("s"), V("e"), V("np"), V("nm")), Call("fairPoissonPointMass", L, V("np"), V("nm"))), N(1))), DivF(Mul(V("A"), Pow(L, Add(V("k"), N(1)))), V("M"))))))));
        return Q("Czero", V("Real"), Imp(Le(N(1), V("Czero")), Ex("A", V("Real"), Ex("Mzero", V("Nat"), Ex("etazero", V("Real"), AndF(LtF(N(0), V("A")), Le(N(1), V("Mzero")), LtF(N(0), V("etazero")), result))))));
    }

}
