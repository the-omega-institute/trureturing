using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class UniformVarianceCenteringDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform variance budget on every unit vector controls simultaneous block means and the full ambient centered Gram operator.",
        H("Uniform variance and block centering"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-variance-hermitian-block-centering-gram"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/UniformVarianceCentering.hermitian_block_centering_and_gram_bound"),
            H("Simultaneous means and the ambient Gram bound"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H and G be arbitrary finite-dimensional complex Hilbert spaces, including the zero space. Let J be any finite index type, V a complex linear isometry from G into H, and h(j) Hermitian complex linear endomorphisms of H. Assume delta is nonnegative and the sum of squared ambient residuals h(j)Vx minus Re(inner(Vx,h(j)Vx))Vx is at most delta for every unit x in G.")),
                Paragraph(Text("Choose an anchor e in G. The anchor is required to have norm one only when G has a unit vector; in a zero block this requirement is vacuous. Define c(j)=Re(inner(Ve,h(j)Ve)), L(j)=h(j)V-c(j)V as a rectangular complex linear map from G into the whole ambient H, and Q=sum(j) L(j) adjoint composed with L(j).")),
                Paragraph(Text("For every unit x, the sum of squared mean displacements from the anchor is at most 4 delta and the sum of squared norms of L(j)x is at most 5 delta. For every vector x, with no normalization, Re(inner(x,Qx)) equals that same ambient energy and is at most 5 delta times norm(x) squared. The operator norm of the actual bounded operator Q is at most 5 delta. For every bounded complex linear endomorphism A of the full ambient H, the actual centered Kraus adjoint sum(j) L(j) adjoint composed with A composed with L(j) has operator norm at most 5 delta times the operator norm of A.")),
                Paragraph(Text("The proof forms the real coefficient direction from the mean displacements. Cauchy-Schwarz controls its scalar variance. Compact Rayleigh extrema of the compressed symmetric operator are eigenvectors; their equal superposition bounds the spectral diameter. A Pythagorean expansion then separates variance from mean displacement. Applying the resulting bound to the actual rectangular residual maps gives the Gram estimate. Cauchy-Schwarz for the two residual-vector families then bounds every matrix coefficient of the centered Kraus adjoint and hence its operator norm.")),
                Paragraph(Text("For a center block of a finite complex matrix direct sum, V is its canonical isometric inclusion and h(j) acts on the entire direct-sum Hilbert space. Thus all components transferred to other center blocks remain in L(j)x and Q. There is no hypothesis that the individual Kraus operators preserve a block. Applying this statement to each nonzero block uses its own anchor; zero factors contribute zero. No spectral simplicity, positive lower eigenvalue, dimension bound, or sum of Kraus squares is needed for this implication.")),
                Paragraph(Text("This is the all-vector implication from the variance hypothesis in C109 equation 86.3 to equation 86.4 and the compressed Gram bound. The passage from the same actual S/H CP-TNI branches to the normalized map, the derivation of equation 86.3 from its Hilbert-Schmidt spectral lower bound, the Hermitian Kraus construction, the centered CP defect identity on the direct sum, and the arbitrary-reference trace-norm estimate remain separate obligations. The original complete Theorem 86.1 is open. Mathematical block vectors and inclusions assert no operational preparation or additional process supply."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var h = F.Id("h"); var v = F.Id("V"); var e = F.Id("e");
        var x = F.Id("x"); var j = F.Id("j"); var d = Delta;
        Formula M(Formula z) => RealPart(Inner(App(v,z), App(At(h,j),App(v,z))));
        var cj = At(F.Id("c"),j); var lj = At(F.Id("L"),j); var q = F.Id("Q");
        var variance = All("x", F.Id("G"), Implies(Unit(x),
            Leq(Sum("j",F.Id("J"),Sq(Norm(Sub(App(At(h,j),App(v,x)),Mul(M(x),App(v,x)))))),d)));
        var assumptions = And(
            All("j",F.Id("J"),Call("IsSymmetric",At(h,j))),
            And(Leq(D(0),d),And(variance,
                Implies(ExistsUnit(),Eqn(Norm(e),D(1))))));
        var definitions = And(All("j",F.Id("J"),Eqn(cj,M(e))),
            And(All("j",F.Id("J"),Eqn(lj,
                Sub(Mul(At(h,j),v),Mul(cj,v)))),
                Eqn(q,Sum("j",F.Id("J"),Mul(Adj(lj),lj)))));
        var unitBounds = All("x",F.Id("G"),Implies(Unit(x),And(
            Leq(Sum("j",F.Id("J"),Sq(Sub(M(x),cj))),Mul(D(4),d)),
            Leq(Energy(x),Mul(D(5),d)))));
        var gram = All("x",F.Id("G"),And(
            Eqn(RealPart(Inner(x,App(q,x))),Energy(x)),
            Leq(RealPart(Inner(x,App(q,x))),Mul(Mul(D(5),d),Sq(Norm(x))))));
        var cp = All("A",Call("ContinuousLinearMap",ComplexType(),F.Id("H"),F.Id("H")),
            Leq(Norm(Sum("j",F.Id("J"),Mul(Adj(lj),Mul(F.Id("A"),lj)))),
                Mul(Mul(D(5),d),Norm(F.Id("A")))));
        var conclusion = All("c",Call("Family",F.Id("J"),RealType()),
            All("L",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("G"),F.Id("H"))),
            All("Q",Call("LinearMap",ComplexType(),F.Id("G"),F.Id("G")),
                Implies(definitions,And(unitBounds,And(gram,And(Leq(Norm(q),Mul(D(5),d)),cp)))))));
        var body = All("V",Call("LinearIsometry",ComplexType(),F.Id("G"),F.Id("H")),
            All("h",Call("Family",F.Id("J"),Call("LinearMap",ComplexType(),F.Id("H"),F.Id("H"))),
            Seq(Forall,Sp,d,Colon,Sp,RealType(),Comma,Sp,
                All("e",F.Id("G"),Implies(assumptions,conclusion)))));
        return All("H",F.Id("Type"),All("G",F.Id("Type"),All("J",F.Id("Type"),
            Seq(Instances("H"),Comma,Sp,Instances("G"),Comma,Sp,
                OpenBracket,Call("Fintype",F.Id("J")),CloseBracket,Comma,Sp,body))));
    }
    private static Formula Instances(string x) => Seq(
        OpenBracket,Call("NormedAddCommGroup",F.Id(x)),CloseBracket,Sp,
        OpenBracket,Call("InnerProductSpace",ComplexType(),F.Id(x)),CloseBracket,Sp,
        OpenBracket,Call("FiniteDimensional",ComplexType(),F.Id(x)),CloseBracket);
    private static Formula ExistsUnit() => Seq(Exists,Sp,F.Id("x"),Colon,Sp,F.Id("G"),Comma,Sp,Unit(F.Id("x")));
    private static Formula Energy(Formula x) => Sum("j",F.Id("J"),Sq(Norm(App(At(F.Id("L"),F.Id("j")),x))));
    private static Formula Unit(Formula x) => Eqn(Norm(x),D(1));
    private static Formula ComplexType() => Seq(Mathbb,Grp(F.Id("C")));
    private static Formula RealType() => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula All(string x,Formula t,Formula b) => Seq(Forall,Sp,F.Id(x),Colon,Sp,t,Comma,Sp,b);
    private static Formula Sum(string x,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(F.Id(x),InMacro,Sp,t),Sp,b);
    private static Formula At(Formula a,Formula i) => Seq(a,Underscore,Grp(i));
    private static Formula App(Formula a,Formula x) => Seq(a,Open,x,Close);
    private static Formula Adj(Formula a) => Seq(a,Caret,Grp(Star));
    private static Formula Inner(Formula a,Formula b) => Call("inner",a,b);
    private static Formula RealPart(Formula a) => Seq(Re,Sp,a);
    private static Formula Norm(Formula a) => Seq(Vert,Sp,a,Sp,Vert);
    private static Formula Sq(Formula a) => Seq(Open,a,Close,Caret,Grp(D(2)));
    private static Formula Mul(Formula a,Formula b) => Seq(a,Sp,b);
    private static Formula Sub(Formula a,Formula b) => Seq(a,Sp,Minus,Sp,b);
    private static Formula Leq(Formula a,Formula b) => Seq(a,Sp,Le,Sp,b);
    private static Formula Eqn(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula And(Formula a,Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula Implies(Formula a,Formula b) => Seq(Open,a,Close,Sp,Rightarrow,Sp,Open,b,Close);
    private static Formula Call(string n,params Formula[] a)
    {
        var parts = new System.Collections.Generic.List<Formula> { Operatorname,Grp(F.Id(n)),Open };
        for (int i=0;i<a.Length;i++) { if (i>0) parts.Add(Comma); parts.Add(a[i]); }
        parts.Add(Close); return Seq(parts.ToArray());
    }
}
