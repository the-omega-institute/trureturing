using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class FiedlerResistanceTripartiteOptimizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete strict Fiedler resistance bound and unique balanced boundary on original labelled tripartite graphs.",
        H("Original tripartite conductances, trace compression and boundary rigidity"),
        Blocks(
            Paragraph(Text("The original parts are the successive intervals of lengths a,b,c in Fin(a+b+c). Every original cross-part edge has its own independent finite real conductance. The competitor domain has no symmetry, invariant-subspace, trace or rank premise. The matrix is the existing counting-measure wLap, lambda2 is its existing nonzero mean-zero Rayleigh infimum, and totalRes is the existing harmonic-current resistance summed once over every unordered distinct original vertex pair, including nonedges. Arbitrary values on unused nonedge coordinates do not enter any uniqueness claim. The source is the repository FIEDLER_RESISTANCE_TRIPARTITE_OPTIMIZER, Lemma 2.1 and Theorem 3.2; no external open-problem or novelty claim is made.")),
            Node("part", "The three original labelled intervals", "part", Triple(All("i", Vert(), Eqn(Part(V("i")),
                Call("ite", Lt(Call("val", V("i")), V("a")), D(0), Call("ite", Lt(Call("val", V("i")), Add(V("a"), V("b"))), D(1), D(2)))))),
                "Part labels are 0,1,2. They keep all original vertices and never contract a part.", DescribeRole.Definition),
            Node("graph", "The labelled complete tripartite graph", "K3", Triple(All("i", Vert(), All("j", Vert(),
                Iff(Adj(V("i"), V("j")), Not(Eqn(Part(V("i")), Part(V("j")))))))),
                "Two original vertices are adjacent exactly when their part labels differ.", DescribeRole.Definition),
            Plain("K3_dec", "Decidable original adjacency", "For all natural a,b,c, the original labelled graph has decidable adjacency.", DescribeRole.Definition),
            Node("boundary", "A zero-extended boundary representative", "boundary", Triple(All("i", Vert(), All("j", Vert(),
                Eqn(App(Bound(), Pair(V("i"), V("j"))), Call("ite", Not(Iff(Eqn(Part(V("i")), D(2)), Eqn(Part(V("j")), D(2)))), Div(D(1), V("c")), D(0)))))),
                "The total Sym2 function is 1/c exactly across the cut from A union B to C and zero elsewhere, including every nonedge and diagonal pair. Consequently its actual original AB edges are zero and its AC and BC edges are 1/c. It is an extremizer only under c=a+b.", DescribeRole.Definition),
            Node("spectrum", "The full spectrum of the actual native Laplacian", "FullSpectrum", Triple(All("w", Weight(),
                Iff(Call("FullSpectrum", V("a"), V("b"), V("c"), V("w")), SpectrumBody()))),
                "The finite index enumeration comes directly from Matrix.IsHermitian.eigenvalues of the actual wLap. Exactly one entry is zero, exactly n-2 entries are one, exactly one is two, and every entry is among these values. This specifies multiplicity without imposing an ascending index order.", DescribeRole.Definition),
            Node("compression", "Trace excess and complete independent-part annihilation", "Compression", Triple(All("w", Weight(),
                Iff(Call("Compression", V("a"), V("b"), V("c"), V("w")), CompressionBody()))),
                "Here H=L-(I-constProj n). The property asserts positive semidefiniteness, annihilation of constants, trace at least one, and, when trace is one, annihilation of every vector of total sum zero supported in any one of the three original parts. The proof sums all original within-part pair-difference Rayleigh inequalities. Their nonnegative gaps vanish simultaneously at trace equality. Positive semidefinite zero energy gives the kernel equations, and the original pair differences span each full supported mean-zero space. This includes part size two and uses no invariant-subspace assumption.", DescribeRole.Definition),
            Node("claim", "Every clause of the original theorem", "Theorem32", Triple(Iff(Call("Theorem32", V("a"), V("b"), V("c")), Conclusion())),
                "The positive product bound is strict and lambda2 is positive. Every nonnegative assignment with actual lambda2=1 has connected positive support and the resistance ceiling. Equality is equivalent to balance and agreement with the displayed boundary on actual original edges. Existence of an equality assignment is equivalent to balance. The balanced boundary is connected, normalized, has the asserted full spectrum and resistance, and has a zero AB edge, so it is outside the positive domain. The final clause supplies Compression for every normalized nonnegative assignment and rank one for its actual excess matrix at resistance equality.", DescribeRole.Definition),
            Node("result", "The complete original Fiedler tripartite theorem", "result", Triple(Imp(Sizes(), Conclusion())),
                "The general harmonic inverse construction supplies R=n times the sum of reciprocal native eigenvalues. The independent parts give trace L at least n*t for actual t=lambda2. On the n-1 positive eigenvalues set q=r/t-1. Then q is nonnegative and its sum is at least one; comparing q/(1+q) to q/(1+sum q) gives the reciprocal ceiling. Equality forces sum q=1 and exactly one q=1. Native unitary diagonalization therefore gives L-t*(I-constProj n)=t*v*v transpose with sum v=0, counting norm one and rank one. Trace equality makes the same v constant on each original part. Same-part off-diagonal entries and part size at least two force each part value to have square 1/n. Equal squares and the original sum-zero equation give the simultaneous sign balance: A and B have the same sign, C the opposite sign, and c=a+b. The actual off-diagonal entries give AB=0 and AC=BC=t/c. Positive conductances exclude this equality. For the boundary, an explicit original-vertex matrix identity L=I-constProj n+(1/n)*sigma*sigma transpose, with sigma equal to +1 on A and B and -1 on C, proves the actual Rayleigh value one. The native eigenvectors then have eigenvalues only 0,1,2; zero multiplicity and trace determine 0,1^(n-2),2. The harmonic spectral identity supplies the attained resistance. This proves all original labelled triples 2<=a<=b<=c, including ties, zeros and asymmetric competitors.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("frto-" + id), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static DocumentBlock Plain(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("frto-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string x) => StrataLint.Scribe.FormulaDsl.Id(x);
    private static Formula C(string x) => new Formula.NamedConstant(FormulaIdentifier.Create(x));
    private static Formula Call(string x, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(x))), [..args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [..args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, f);
    private static Formula Ex(string x, Formula t, Formula f) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, f);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula In(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Or, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
    private static Formula Not(Formula f) => new Formula.Not(Par(f));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Triple(Formula f) => All("a", C("Nat"), All("b", C("Nat"), All("c", C("Nat"), f)));
    private static Formula N() => Add(Add(V("a"),V("b")),V("c"));
    private static Formula Vert() => Call("Fin", N());
    private static Formula Weight() => Seq(Call("Sym2", Vert()), Sp, To, Sp, C("Real"));
    private static Formula Vector() => Seq(Vert(), Sp, To, Sp, C("Real"));
    private static Formula G() => Call("K3", V("a"),V("b"),V("c"));
    private static Formula Bound() => Call("boundary",V("a"),V("b"),V("c"));
    private static Formula Part(Formula i) => Call("part",V("a"),V("b"),V("c"),i);
    private static Formula Adj(Formula i, Formula j) => Call("Adj",G(),i,j);
    private static Formula Pair(Formula i, Formula j) => Seq(V("s"),Open,i,Comma,j,Close);
    private static Formula Lap(Formula w) => Call("wLap",G(),w);
    private static Formula Lambda(Formula w) => Call("lambda2",G(),w);
    private static Formula R(Formula w) => Call("totalRes",G(),w);
    private static Formula U() => Mul(N(),Sub(N(),Div(D(3),D(2))));
    private static Formula Positive(Formula w, bool strict) => All("i",Vert(),All("j",Vert(),Imp(Adj(V("i"),V("j")),
        strict ? Lt(D(0),App(w,Pair(V("i"),V("j")))) : Leq(D(0),App(w,Pair(V("i"),V("j")))))));
    private static Formula Connected(Formula w) => Call("Connected",Call("support",G(),w));
    private static Formula EdgeEqual(Formula w) => All("i",Vert(),All("j",Vert(),Imp(Adj(V("i"),V("j")),Eqn(App(w,Pair(V("i"),V("j"))),App(Bound(),Pair(V("i"),V("j")))))));
    private static Formula Hmat() => Sub(Lap(V("w")),Par(Sub(D(1),Call("constProj",N()))));
    private static Formula Eigen(Formula i) => App(Call("eigenvalues",Lap(V("w"))),i);
    private static Formula Count(Formula value) => Call("card",Call("filter",Par(Seq(LambdaLower,Sp,V("i"),Sp,Mapsto,Sp,Eqn(Eigen(V("i")),value))),Call("univ",Vert())));
    private static Formula SpectrumBody() => And(Eqn(Count(D(0)),D(1)),And(Eqn(Count(D(1)),Sub(N(),D(2))),And(Eqn(Count(D(2)),D(1)),
        All("i",Vert(),Or(Eqn(Eigen(V("i")),D(0)),Or(Eqn(Eigen(V("i")),D(1)),Eqn(Eigen(V("i")),D(2))))))));
    private static Formula CompressionBody() => And(Call("PosSemidef",Hmat()),And(Eqn(Call("mulVec",Hmat(),D(1)),D(0)),And(Leq(D(1),Call("trace",Hmat())),
        Imp(Eqn(Call("trace",Hmat()),D(1)),All("r",C("Nat"),Imp(In(V("r"),Seq(OpenBrace,D(0),Comma,D(1),Comma,D(2),CloseBrace)),
            All("x",Vector(),Imp(Eqn(Call("sum",V("x")),D(0)),Imp(All("i",Vert(),Imp(Not(Eqn(Part(V("i")),V("r"))),Eqn(App(V("x"),V("i")),D(0)))),Eqn(Call("mulVec",Hmat(),V("x")),D(0)))))))))));
    private static Formula Sizes() => And(Leq(D(2),V("a")),And(Leq(V("a"),V("b")),Leq(V("b"),V("c"))));
    private static Formula Conclusion()
    {
        Formula w=V("w");
        Formula positive=All("w",Weight(),Imp(Positive(w,true),And(Lt(D(0),Lambda(w)),Lt(Mul(Lambda(w),R(w)),U()))));
        Formula normalized=All("w",Weight(),Imp(Positive(w,false),Imp(Eqn(Lambda(w),D(1)),And(Connected(w),And(Leq(R(w),U()),Iff(Eqn(R(w),U()),And(Eqn(V("c"),Add(V("a"),V("b"))),EdgeEqual(w))))))));
        Formula exists=Iff(Ex("w",Weight(),And(Positive(w,false),And(Eqn(Lambda(w),D(1)),Eqn(R(w),U())))),Eqn(V("c"),Add(V("a"),V("b"))));
        Formula boundary=Imp(Eqn(V("c"),Add(V("a"),V("b"))),And(Positive(Bound(),false),And(Connected(Bound()),And(Eqn(Lambda(Bound()),D(1)),And(Eqn(R(Bound()),U()),And(Call("FullSpectrum",V("a"),V("b"),V("c"),Bound()),Not(Positive(Bound(),true))))))));
        Formula compression=All("w",Weight(),Imp(Positive(w,false),Imp(Eqn(Lambda(w),D(1)),And(Call("Compression",V("a"),V("b"),V("c"),w),Imp(Eqn(R(w),U()),Eqn(Call("rank",Hmat()),D(1)))))));
        return And(positive,And(normalized,And(exists,And(boundary,compression))));
    }
}
