using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativeSuppliedWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSuppliedWidth",H("Attained complete-word widths"),Blocks(
            Paragraph(Text("An Installation of positive width w has an arbitrary finite type of complete mutable states and an injection of all of them into the no-adjacent-ones words of length w. Each state selects a fixed literal and a successor for every raw Read reply, a genuine Update successor, a fixed-output halt, or an arbitrary deterministic source-blind internal step. Every primitive response changes at most one bit, with hold allowed. Internal transitions have no additional bit-change restriction. All states, including unreachable ones, are encoded and counted.")),
            Paragraph(Text("Feasible(S,T,w) asserts that such an installation is correct on every independent original assignment and every entry from zero through T on the single supplied skeleton. StaticFeasible additionally requires zero actual Updates on every promised successful run. The inverse capacity d(n), for positive n, is the existing stage dimension at n minus one: it is the least d with n at most fib(d+2). Thus it counts the full admissible word space. The minima a(S,T) and s(S,T) range over the entire respective classes.")),
            Paragraph(Text("Generality I: the substitution, binary no-adjacent-ones language, Fibonacci capacity and golden-ratio base are fixed. The bounds are uniform over every supplied skeleton, even leaf count and finite lag promise within this family. The logarithmic estimate relies on the instance supplier AxisConvergence.goldenRatio_pow_div_le_fib_succ; extending it to other recurrences or quadratic families requires further results.")),
            Describe("native-upper-members","D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.native_upper_members",
                "Native members of both full classes",Upper(),
                "For even h, set K=(T+1)/2 and M=h(K+1). The active and static full-table encodings are injected on every installed state and satisfy every typed primitive row, including all four raw replies. The existing original-source native executions are connected to Run in both directions. Sourcewise termination and deterministic output then give correctness, and the static table's rows exclude every actual Update. These concrete members establish nonemptiness without assuming abstract upper bounds. Since an actual source has positive leaf count, even h implies h at least two."),
            Describe("minimum-width-bounds","D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.minimum_width_bounds",
                "Attainment and inverse-capacity bounds",Bounds(),
                "The well-ordering of natural widths gives an attained least width in each nonempty full class. The distinct-query and static-cover counts give their lower capacity bounds. The delivered native members give the upper bounds. Capacity is monotone, and the Fibonacci recurrence gives d(2n) at most d(n)+2. Since K+1 is at most twice r=(T+3)/3, this gives the final static additive constant nine. The domain retains even h and the full lag interval for all supplied shapes."),
            Describe("uniform-logarithmic-width","D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.uniform_logarithmic_width",
                "Uniform coefficient one",Logs(),
                "The existing golden-ratio power lower bound and the pinned Fibonacci identity bound fib(d+2) between phi to the power d and phi to the power d+1. Minimality of inverse capacity then places d(n) within one of log base phi of n. Combining the attained-width bounds with capacity doubling gives absolute error at most ten for both displayed logarithms. Ten is a proved uniform constant, independent of the skeleton, its unequal original leaf depths, h, and T. These estimates concern word width; they imply no optimum for other resource coordinates or physical cost."))));

    private static Formula Even(Formula h) => Eqn(C("mod",h,D(2)),D(0));
    private static Formula WidthBody(Func<Formula,Formula,Formula,Formula> f) {
        var s=V("S");var t=V("T");var h=C("length",s);
        return All("S",V("Source"),All("T",V("Nat"),Imp(Even(h),f(s,t,h))));
    }
    private static Formula Upper() => WidthBody((s,t,h) => {
        var m=Times(h,PlusOf(C("div",PlusOf(t,D(1)),D(2)),D(1)));
        return A(C("Feasible",s,t,PlusOf(C("dimension",h),D(7))),C("StaticFeasible",s,t,PlusOf(C("dimension",m),D(7))));
    });
    private static Formula Bounds() => WidthBody((s,t,h) => {
        var a=C("activeMinimum",s,t);var b=C("staticMinimum",s,t);var w=V("w");
        var r=C("div",PlusOf(t,D(3)),D(3));var m=Times(h,PlusOf(C("div",PlusOf(t,D(1)),D(2)),D(1)));
        var dh=C("capacity",PlusOf(h,D(2)));var dhs=C("capacity",PlusOf(h,D(1)));
        var dq=C("capacity",PlusOf(Times(h,r),D(2)));var dm=C("capacity",PlusOf(m,D(1)));
        return A(C("Feasible",s,t,a),A(All("w",V("Nat"),Imp(C("Feasible",s,t,w),Le(a,w))),
            A(C("StaticFeasible",s,t,b),A(All("w",V("Nat"),Imp(C("StaticFeasible",s,t,w),Le(b,w))),
            A(Le(dh,a),A(Le(a,PlusOf(dhs,D(7))),A(Le(PlusOf(dhs,D(7)),PlusOf(dh,D(7))),
            A(Le(dq,b),A(Le(b,PlusOf(dm,D(7))),Le(PlusOf(dm,D(7)),PlusOf(dq,D(9))))))))))));
    });
    private static Formula Logs() => WidthBody((s,t,h) => A(
        Le(Abs(Seq(C("activeMinimum",s,t),Sp,Minus,Sp,C("logb",V("phi"),h))),D(1,0)),
        Le(Abs(Seq(C("staticMinimum",s,t),Sp,Minus,Sp,C("logb",V("phi"),Times(h,PlusOf(t,D(1)))))),D(1,0))));

    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula f) => Seq(Open,f,Close);
    private static Formula C(string n,params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,P(b));
    private static Formula A(Formula a,Formula b) => Seq(P(a),Sp,Land,Sp,P(b));
    private static Formula Imp(Formula a,Formula b) => Seq(P(a),Sp,Implies,Sp,P(b));
    private static Formula Eqn(Formula a,Formula b) => Seq(a,Sp,F.Eq,Sp,b);
    private static Formula Le(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula PlusOf(Formula a,Formula b) => Seq(P(a),Sp,Plus,Sp,P(b));
    private static Formula Times(Formula a,Formula b) => Seq(P(a),P(b));
    private static Formula Abs(Formula a) => Seq(Lvert,Sp,a,Rvert,Sp);
    private static DocumentBlock.Describe Describe(string id,string declaration,string title,Formula statement,string text) =>
        DescribeNode(id,declaration,title,statement,text);
    private static DocumentBlock.Describe DescribeNode(string id,string declaration,string title,Formula statement,string text) =>
        global::StrataLint.Scribe.Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(declaration),H(title),
            StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
}
