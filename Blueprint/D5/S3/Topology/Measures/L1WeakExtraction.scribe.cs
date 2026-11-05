using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class L1WeakExtractionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/L1WeakExtraction.";
    private static Formula V(string n) => F.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Inst(string n, Formula t) =>
        Seq(OpenBracket, Call(n, t), CloseBracket, Sp);
    private static Formula N => Call("Nat");
    private static Formula Real => Call("Real");
    private static Formula Ty(string n) => Seq(V("Type"), Underscore, Grp(V(n)));
    private static Formula At(Formula f, Formula x) => Call("apply", f, x);
    private static Formula At(Formula f, Formula x, Formula y) => At(At(f, x), y);
    private static Formula Dual(Formula x) => Call("ContinuousRealLinearFunctional", x);
    private static Formula Norm(Formula x) => Call("norm", x);
    private static Formula Bounds() => Grp(Seq(All("m", N), All("n", N),
        Norm(At(V("t"), V("m"), V("n"))), Sp, Le, Sp, At(V("R"), V("m"))));
    private static Formula Weak(Formula x, Formula y) =>
        Call("Tendsto", Seq(V("n"), Sp, Mapsto, Sp, x), Call("atTop"), Call("nhds", y));
    private static Formula Hilbert() => Seq(All("H", Ty("v")),
        Inst("NormedAddCommGroup", V("H")), Inst("RealInnerProductSpace", V("H")),
        Inst("CompleteSpace", V("H")));
    private static Formula Common() => Disp(new Formula.Aligned([
        Hilbert(),
        Seq(All("t", Fn(N, Fn(N, V("H")))), All("R", Fn(N, Real)), Bounds(), Sp, Rightarrow),
        Seq(Exists, Sp, V("j"), Colon, Fn(N, N), Comma, Sp,
            Exists, Sp, V("q"), Colon, Fn(N, V("H")), Comma, Sp,
            Call("StrictMono", V("j")), Sp, Land, Sp,
            All("m", N), All("phi", Dual(V("H"))),
            Weak(At(V("phi"), At(V("t"), V("m"), At(V("j"), V("n")))),
                At(V("phi"), At(V("q"), V("m")))))
    ]));
    private static Formula Approximation() => Disp(new Formula.Aligned([
        Seq(All("X", Ty("u")), Inst("NormedAddCommGroup", V("X")),
            Inst("RealNormedSpace", V("X")), Inst("CompleteSpace", V("X"))),
        Hilbert(),
        Seq(All("T", Call("ContinuousRealLinearMap", V("H"), V("X"))),
            All("f", Fn(N, V("X"))), All("t", Fn(N, Fn(N, V("H"))))),
        Seq(All("R", Fn(N, Real)), All("delta", Fn(N, Real)), Bounds(), Sp, Rightarrow),
        Seq(Call("Tendsto", V("delta"), Call("atTop"), Call("nhds", D(0))), Sp, Rightarrow),
        Seq(Grp(Seq(All("m", N), All("n", N),
            Norm(Seq(At(V("f"), V("n")), Sp, Minus, Sp,
                At(V("T"), At(V("t"), V("m"), V("n"))))), Sp, Le, Sp,
            At(V("delta"), V("m")))), Sp, Rightarrow),
        Seq(Exists, Sp, V("j"), Colon, Fn(N, N), Comma, Sp,
            Exists, Sp, V("v"), Colon, V("X"), Comma, Sp,
            Call("StrictMono", V("j")), Sp, Land, Sp,
            All("phi", Dual(V("X"))),
            Weak(At(V("phi"), At(V("f"), At(V("j"), V("n")))), At(V("phi"), V("v"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded Hilbert approximations yield weak subsequences in complete real normed spaces.",
        H("Weak extraction through Hilbert approximation"),
        Blocks(
            Paragraph(Text("The weak convergence below tests every continuous real linear functional. "
                + "No separability assumption is imposed on either ambient space, and the zero space is included. "
                + "The maps denoted apply in the formulas are ordinary function evaluation.")),
            Describe.Lean(DescribeId.Create("common-weak-subsequence"),
                DeclarationHandle.Create(Owner + "exists_common_weak_subsequence"),
                H("A common subsequence for countably many bounded Hilbert sequences"),
                StatementSource.FromAuthor(Common()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The countable family t(m,n) lies in the closed span of its range indexed by Nat × Nat. "
                    + "That closed span is complete and separable. Riesz representation sends each bounded row into a compact metrizable weak dual ball. "
                    + "Sequential compactness of the countable product gives one increasing selector for all rows. "
                    + "Riesz representation and symmetry of the real inner product turn convergence of dual evaluations into convergence against every functional. "
                    + "Restricting an ambient functional to the closed span then gives the stated conclusion. "
                    + "No continuity from the weak dual topology to the norm topology is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weak-subsequence-hilbert-approximation"),
                DeclarationHandle.Create(Owner + "exists_weak_subsequence_of_hilbert_approximation"),
                H("Uniform norm approximation produces a genuine weak limit"),
                StatementSource.FromAuthor(Approximation()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The errors delta(m) tend to zero uniformly in the sequence index; their nonnegativity follows from the norm bounds. "
                    + "Apply the common Hilbert selector and transfer each row through T. "
                    + "Hahn–Banach gives a functional of norm at most one that norms the difference of any two row limits, including a zero difference. "
                    + "Passing the uniform approximation bound to its scalar limit shows that the row limits are norm Cauchy. "
                    + "Completeness gives their norm limit; a three-term estimate proves convergence of the selected original sequence against an arbitrary functional. "
                    + "This is the weak-extraction mechanism for hard truncations in real L1 over a finite measure. "
                    + "It does not construct the disjoint carriers of subsequence splitting or resolve the signed CH construction or Problem 8.2."))), DescribeRole.Theorem))));
}
