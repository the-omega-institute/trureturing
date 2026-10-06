using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class InteriorRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/InteriorRoot.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Side => I("MemorySide");
    private static Formula Int => I("Int");
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Seq => Fn(Int,I("CuLetter"));
    private static Formula Lam(string n, Formula t, Formula p) => new Formula.Sequence(p,I(n),t);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Div(Formula a, Formula b) => Call("divide",a,b);
    private static Formula Mem(Formula a, Formula b) => Call("member",a,b);
    private static Formula Subset(Formula a, Formula b) => Call("subset",a,b);
    private static Formula Lower => I("lower");
    private static Formula Upper => I("upper");
    private static Formula High => Call("hSide",I("high"));
    private static Formula Next => Add(I("n"),D(1));
    private static Formula Language(Formula side, Formula n) => Call("MemoryLanguage",side,n,I("K"),I("d"));
    private static Formula Aux => Call("AuxiliaryLanguage",I("K"),I("d"));
    private static Formula Rate(Formula x) => Call("weightedFactorRate",x);
    private static Formula Radius(Formula side, Formula n, Formula z) => Call("weightedRadius",side,n,I("K"),I("d"),z);
    private static Formula Value(Formula z) => Call("radiusValue",I("side"),I("n"),I("K"),I("d"),z);
    private static Formula Matrix(Formula z) => Call("complexAdjacency",I("side"),I("n"),I("K"),I("d"),z);
    private static Formula Core => Call("CoreVertex",I("side"),I("n"),I("K"),I("d"));
    private static Formula Mass(Formula z, Formula k) => Call("pathMass",I("side"),I("n"),I("K"),I("d"),z,k);
    private static Formula Source(Formula p) => All(p,B("side",Side),B("n",Nat),B("K",Nat),B("d",Real));
    private static Formula SourceZ(Formula p) => Source(All(p,B("z",Real)));
    private static Formula RootScope(Formula p) => Source(Imp(And(Le(D(2),I("K")),Le(I("K"),I("n"))),p));
    private static Formula Past(Formula n, Formula seed) => Call("finitePast",I("omega"),I("i"),n,seed);
    private static Formula State => Call("pastState",I("omega"),I("i"));
    private static Formula Gamma(Formula z) => Call("negate",Call("logb",D(2),z));
    private static Formula RootBody(Formula z, bool rate) => rate
        ? And(Lt(D(0),z),Lt(z,D(1)),Equal(Radius(I("side"),I("n"),z),D(1)),Equal(Rate(Language(I("side"),I("n"))),Gamma(z)))
        : And(Lt(D(0),z),Lt(z,D(1)),Equal(Radius(I("side"),I("n"),z),D(1)));
    private static Formula Root(bool rate) => RootScope(Call("existsUnique",Lam("z",Real,RootBody(I("z"),rate))));
    private static Formula Nesting(bool rates)
    {
        Formula[] languages=[Language(Lower,I("n")),Language(Lower,Next),Aux,Language(Upper,Next),Language(Upper,I("n"))];
        Formula[] clauses=new Formula[4];
        for(var k=0;k<4;k++) clauses[k]=rates ? Le(Rate(languages[k]),Rate(languages[k+1])) : Subset(languages[k],languages[k+1]);
        return All(And(clauses),B("n",Nat),B("K",Nat),B("d",Real));
    }
    private static Formula Envelopes() => All(And(
        Le(Past(I("n"),D(0)),Past(Next,D(0))),Le(Past(Next,High),Past(I("n"),High)),
        Le(Past(I("n"),D(0)),State),Le(State,Past(I("n"),High)),
        Le(Sub(Past(I("n"),High),Past(I("n"),D(0))),Mul(High,Pow(I("rho"),I("n"))))),
        B("omega",Seq),B("i",Int),B("n",Nat));
    private static Formula Literal()
    {
        var digits=All(Equal(Call("lowSequence",I("choices"),Add(Mul(D(5),I("j")),Call("toInt",I("k")))),
            Call("get",Call("lowBlock",Call("choices",I("j"))),I("k"))),B("j",Int),B("k",Call("Fin",D(5))));
        return All(Imp(Le(D(2),I("K")),And(digits,
            Mem(Call("lowSequence",I("choices")),Call("LowCapLanguage",I("K"))))),B("choices",Fn(Int,I("Bool"))),B("K",Nat));
    }
    private static Formula AllU() => SourceZ(Imp(Le(D(0),I("z")),Ex(And(
        Call("MemoryEdge",I("side"),I("K"),I("d"),Call("val",I("v")),I("u"),Call("val",I("v"))),
        All(Le(Pow(Pow(I("z"),D(6)),I("k")),Mass(I("z"),I("k"))),B("k",Nat))),B("v",Core))));
    private static Formula Families()
    {
        Formula RootAt(Formula side, Formula n) => Call("roots",side,n);
        var z=RootAt(I("side"),I("n"));
        var properties=All(Imp(Le(I("K"),I("n")),And(Lt(D(0),z),Lt(z,D(1)),
            Equal(Radius(I("side"),I("n"),z),D(1)),Equal(Rate(Language(I("side"),I("n"))),Gamma(z)))),B("side",Side),B("n",Nat));
        var sandwich=All(Imp(Le(I("K"),I("n")),And(Le(Gamma(RootAt(Lower,I("n"))),Rate(Aux)),
            Le(Rate(Aux),Gamma(RootAt(Upper,I("n")))))),B("n",Nat));
        var increasing=Call("MonotoneOn",Lam("n",Nat,Gamma(RootAt(Lower,I("n")))),Call("Ici",I("K")));
        var decreasing=Call("AntitoneOn",Lam("n",Nat,Gamma(RootAt(Upper,I("n")))),Call("Ici",I("K")));
        return All(Imp(Le(D(2),I("K")),Ex(And(properties,sandwich,increasing,decreasing),
            B("roots",Fn(Side,Fn(Nat,Real))))),B("K",Nat),B("d",Real));
    }
    private static DocumentBlock Node(string name, Formula statement, string prose, DescribeRole role=DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("fib-interior-root-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
        H(name.Replace('_',' ')),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both original retained memory graphs have a unique interior weighted spectral root whose binary logarithm is their actual weighted factor rate.",
        H("Original interior weighted spectral roots"),Blocks(
        Paragraph(Text("The graphs retain the original finite-past vertices, strict lower and closed upper guards, both letter labels and their weights twenty and six. All vertices and allowed edges on bilateral paths remain, including parallel labels, reducible components and transient bridges. The threshold d is any real number. Interior roots require n at least K at least two; the separate K=1 closed-root boundary is preserved.")),
        Node("LowCapLanguage",All(Equal(Call("LowCapLanguage",I("K")),Call("setOf",Lam("omega",Seq,
            All(new Formula.Not(All(Equal(Call("omega",Add(I("i"),Call("toInt",I("k")))),I("c")),
                B("k",Call("Fin",I("K"))))),B("i",Int))))),B("K",Nat)),
            "The low cap is the full bilateral language with no forward c run of length K. It is the original cap K minus one; it has no threshold or supplied entropy parameter.",DescribeRole.Definition),
        Node("lowBlock",All(Equal(Call("lowBlock",I("b")),Call("ifThenElse",I("b"),
            Call("list",I("c"),I("u"),I("u"),I("c"),I("u")),Call("list",I("c"),I("u"),I("c"),I("u"),I("u")))),B("b",I("Bool"))),
            "The true and false binary choices select precisely the two distinct five-letter words. Both words have two c letters and three u letters, so their original total weight is fifty-eight.",DescribeRole.Definition),
        Node("lowSequence",All(Equal(Call("lowSequence",I("choices"),I("i")),Call("ifThenElse",
            Or(Equal(Call("intMod",I("i"),D(5)),D(0)),Equal(Call("intMod",I("i"),D(5)),
                Call("ifThenElse",Call("choices",Call("intDivide",I("i"),D(5))),D(3),D(2)))),I("c"),I("u"))),
            B("choices",Fn(Int,I("Bool"))),B("i",Int)),
            "Integer quotient and remainder choose the bilateral block and its position. Position zero is c; the second c is at position three for true and position two for false. All other positions are u.",DescribeRole.Definition),
        Node("original_low_cap_inclusion",Source(Imp(Lt(D(0),I("K")),Subset(Call("LowCapLanguage",I("K")),Language(I("side"),I("n"))))),
            "The complete language with no c run of length K lies in both memories. A run of length K+1 would contain a forbidden K run. Reversing the high-run test excludes every high guard, independently of its threshold and strictness."),
        Node("literal_bilateral_low_codebook",Literal(),
            "The literal blocks c u c u u and c u u c u occupy fixed five-letter cuts. Integer quotient and remainder construct one sequence for every bilateral binary choice, including negative indices. Adjacent c letters are impossible within a block or across its final u and the next initial c. Thus every K at least two has the required low-cap realization."),
        Node("original_memory_envelopes",Envelopes(),
            "Increasing memory raises the zero-seed image and lowers the h-seed image. Positive slopes and the invariant interval prove these finite inequalities. The existing bilateral limits place the actual state between the two images; the exact weighted contraction bounds their difference by h times rho to n."),
        Node("original_memory_language_nesting",Nesting(false),
            "The lower language at n is contained in the lower language at n+1, then in the original auxiliary language. The auxiliary language is contained in the upper language at n+1, then in the upper language at n. Each implication applies the corresponding actual envelope to the same pre-transition high guard."),
        Node("original_upper_memory_intersection",All(Equal(Call("setOf",Lam("omega",Seq,
            All(Imp(Le(I("K"),I("n")),Mem(I("omega"),Language(Upper,I("n")))),B("n",Nat)))),Aux),B("K",Nat),B("d",Real)),
            "Passing to the actual limit of all upper-seed images gives precisely the closed auxiliary guard. Conversely that actual guard lies below every upper envelope. Equality at the guard threshold is therefore retained in every upper memory."),
        Node("original_literal_codebook_growth",Source(All(Imp(Le(D(2),I("K")),Le(Pow(D(2),I("q")),
            Call("factorCount",Language(I("side"),I("n")),Mul(I("q"),D(5,8))))),B("q",Nat))),
            "Every q-bit choice extends to a bilateral sequence using the two literal blocks. Both blocks have weight fifty-eight. Equal positive weighted cuts recover the ordered blocks, and their different third letters recover the bits. This constructs an injection of all 2 to q choices into factors of weight 58q, including q=0."),
        Node("original_positive_weighted_rate",Source(Imp(Le(D(2),I("K")),Le(Div(D(1),D(5,8)),Rate(Language(I("side"),I("n")))))),
            "Counts at all multiples of fifty-eight give a lower bound of one over fifty-eight for the original max-one weighted factor limsup. The bound uses actual source-step weights, rather than the five-letter block length."),
        Node("original_memory_rate_nesting",Nesting(true),
            "Factor inclusion injects each fixed-weight dictionary. Nonnegative series comparison and the exact weighted convergence abscissa transfer this inclusion to rates. Applying it to the constructed language nesting gives the two rate monotonicities and the auxiliary sandwich."),
        Node("original_all_u_cycle",AllU(),
            "The constant u memory is an actual retained vertex and has an allowed u self-edge for every defined memory and threshold. Its k-step CorePath contributes exactly z to 6k. Every other monomial is nonnegative when z is nonnegative, so the full path mass dominates this cycle."),
        Node("original_spectral_positive",SourceZ(Imp(Lt(D(0),I("z")),Le(Call("ENNRealOfReal",Pow(I("z"),D(6))),Radius(I("side"),I("n"),I("z"))))),
            "A spectral radius below z to six would give a geometric bound with a strictly smaller rate. The actual u-cycle monomials contradict that bound as k grows. Hence every positive z has positive spectral radius."),
        Node("radiusValue",SourceZ(Equal(Value(I("z")),Call("toReal",Radius(I("side"),I("n"),I("z"))))),
            "RadiusValue is the real value of the original complex spectral radius. The actual all-u vertex makes the retained carrier nonempty, and the norm bound proves that the spectral radius is finite.",DescribeRole.Definition),
        Node("original_radius_scaling",Source(All(Imp(And(Lt(D(0),I("x")),Le(I("x"),I("y"))),And(
            Le(Mul(Pow(Div(I("y"),I("x")),D(6)),Value(I("x"))),Value(I("y"))),
            Le(Value(I("y")),Mul(Pow(Div(I("y"),I("x")),D(2,0)),Value(I("x")))))),B("x",Real),B("y",Real))),
            "Each genuine k-letter monomial has weight between 6k and 20k. Comparing their sums bounds the actual power masses. The norm sandwich and geometric power estimates pass these bounds to spectral radii through Gelfand's formula, without any irreducibility condition."),
        Node("original_radius_strict_increase",Source(Call("StrictMonoOn",Lam("z",Real,Value(I("z"))),Call("Ioi",D(0)))),
            "For y greater than x greater than zero, the factor (y/x) to six exceeds one. The lower scaling bound and actual spectral positivity make the original real spectral radius strictly increase."),
        Node("original_adjacency_zero_continuous",Source(And(Equal(Matrix(D(0)),D(0)),Call("Continuous",Lam("z",Real,Matrix(I("z")))))),
            "All actual edge exponents are positive, so the matrix at zero is zero. Each entry is a fixed finite sum of the two real monomials, carried into the complex numbers, and is continuous."),
        Node("original_radius_continuous",Source(Call("ContinuousOn",Lam("z",Real,Value(I("z"))),Call("Ici",D(0)))),
            "At a positive parameter, the scaling bounds squeeze the radius between the minimum and maximum of the sixth and twentieth powers of the parameter ratio. Both envelopes meet the same radius. At zero, the continuous matrix norm tends to zero and dominates the nonnegative radius. These two arguments give continuity on the full nonnegative half-line."),
        Node("original_spectral_at_one",RootScope(Lt(D(1),Value(D(1)))),
            "The literal weighted rate bound forces divergence at a positive binary parameter strictly below one. The exact original factor-series boundary makes its spectral radius at least one; strict increase then makes the radius at one exceed one."),
        Node("original_interior_root",Root(false),
            "The actual spectral radius is zero at zero and exceeds one at one. Continuity supplies an interior radius-one parameter, and strict increase makes it unique. The construction applies to both full retained graphs and every real d whenever n is at least K and K is at least two."),
        Node("original_weighted_interior_root",Root(true),
            "Let gamma be minus log base two of the constructed root. Positivity and the root's upper bound make gamma positive. Strict increase identifies the actual convergence exponents with the open interval above gamma. The already established weighted factor-rate infimum therefore equals gamma, including sparse unsupported weights and the max-one convention."),
        Node("original_root_rate_families",Families(),
            "Choose the unique interior root at every admissible memory length for both sides. Its logarithmic rate equals the actual memory-language rate. The proven lower and upper language nesting gives the auxiliary-rate sandwich, increasing lower root rates and decreasing upper root rates on n at least K. Values below K are only a total-function convention and carry no interior-root claim."),
        Paragraph(Text("The auxiliary rate is the original actual-list rate under the fixed transition-budget assumptions and the complete actual-language rate bridge. This identifies the sandwich with eta_b for both prescribed actual initial states. Fixed-graph common margins, pressure convergence, eventual even-length asymptotics and the remaining canonical-path, storage and optimum conclusions require their respective further results.")))));
}
