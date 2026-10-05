using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitCoarseLowerBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two subset potentials bound every probability law of coarse-observable original controllers, including laws with infinite expected costs.",
        H("Four-Exit Coarse Controller Lower Bounds"),
        Blocks(
            Paragraph(Text("For k at least one, I(k)=Unit plus Fin(k) times Fin(4), and n(k)=8k+16. F(k,i) is the existing literal family from FourExitRawEndpointSpectrum. The baseline is the Unit row; rows zero, one, two and three in a slot are A, Y, H and Z. The Strategy, chronological execution, terminal history, distinct-address cost, leaf addresses and coarse observability are the existing actual-tree interfaces. Every Strategy is globally correct on all finite sources; neither a family promise nor a uniform termination bound is assumed.")),
            Paragraph(Text("A law consists of any measurable space Omega, a probability measure mu on it, and an arbitrary choice c:Omega to Strategy. Every c(omega) is coarse-observable, and each coordinate omega to C_i(c(omega)) is measurable as an extended nonnegative real function. No finite support, measurable controller carrier or finiteness of expectation is required. R is the supremum of the coordinate expectations. D is the infimum, over all coarse-observable original Strategies, of their worst coordinate cost. W is the expectation of the supremum of coordinate costs. All expectations are nonnegative Lebesgue integrals and can be infinite.")),
            Describe.Lean(DescribeId.Create("four-exit-coarse-lower-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds.result"),
                H("Arbitrary Laws and Deterministic Two-Excess Obstruction"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A finite fuel chosen from the actual terminating executions produces a finite coarse tree with the original terminal histories. At any none branch, saturation and fresh divergence imply that at most one row in a counting subset has excess below two. Following the leaf branch therefore yields a charge inequality for every subset.")),
                    Paragraph(Text("For all nonbaseline rows the potential sums min(column size,3). The actual support table excludes a leaf support of size three, so every relevant none deletion drops this potential. For the A,Y,Z subset the potential sums min(triple size,2); a one-unit credit accounts for its possible nondropping deletion. The actual common compensation support ensures that this exception occurs at most once. At the root these yield total excess at least 5k-1 and 4k-2, respectively. Finite-sum integration and averaging give the two bounds on R.")),
                    Paragraph(Text("On the baseline together with any four-row slot, the actual support table excludes a leaf child of size four. The first information query thus has at least two none rows. Their subsequent fresh divergence forces one row to pay a second nonleaf. This gives a deterministic row of cost at least n+2, the infimum bound on D and the pointwise bound whose integral yields W."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula k=V("k"), n=Call("n",k), mu=V("mu"), c=V("c"), pi=V("pi");
        Formula two=Add(n,D(2));
        Formula deterministic=All("pi",V("Strategy"),Imp(Call("CoarseObservable",Call("policy",pi)),
            Some("i",Call("I",k),Le(two,Call("C",k,V("i"),pi)))));
        Formula law=And(Call("CoarseLaw",k,mu,c),Call("MeasurableCosts",k,c));
        Formula conclusion=And(
            Le(Add(n,Fr(Subtract(Multiply(D(5),k),D(1)),Multiply(D(4),k))),Call("R",k,mu,c)),
            Le(Add(n,Fr(Subtract(Multiply(D(4),k),D(2)),Multiply(D(3),k))),Call("R",k,mu,c)),
            deterministic,Le(two,Call("D",k)),Le(two,Call("W",k,mu,c)));
        return Disp(All("k",V("Nat"),Imp(Le(D(1),k),
            All("Omega",V("MeasurableSpace"),All("mu",Call("Probability",V("Omega")),
                All("c",Call("Controllers",V("Omega")),Imp(law,conclusion)))))));
    }
}
