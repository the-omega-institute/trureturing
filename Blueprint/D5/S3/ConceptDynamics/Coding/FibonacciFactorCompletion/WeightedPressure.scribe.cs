using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class WeightedPressureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WeightedPressure.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Config => Fn(I("Int"),I("CuLetter"));
    private static Formula Language => Call("Set",Config);
    private static Formula Word => Call("List",I("CuLetter"));
    private static Formula Lam(string n, Formula t, Formula p) => F.Seq(Open, I(n), Sp, Colon, Sp, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Sum(string n, Formula t, Formula p) => Call("sum",Lam(n,t,p));
    private static Formula Tsum(string n, Formula t, Formula p) => Call("tsum",Lam(n,t,p));
    private static Formula Summable(string n, Formula t, Formula p) => Call("Summable",Lam(n,t,p));
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Div(Formula a, Formula b) => Call("divide",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Neg(Formula a) => Call("negate",a);
    private static Formula R(Formula a) => Call("toReal",a);
    private static Formula ER(Formula a) => Call("ofReal",a);
    private static Formula Val(Formula a) => Call("val",a);
    private static Formula Occupied => Call("Nonempty",I("X"));
    private static Formula Dictionary(Formula k) => Call("LengthDictionary",I("X"),k);
    private static Formula Words => Call("OccurringWord",I("X"));
    private static Formula Weight(Formula w) => Call("wordWeight",w);
    private static Formula Length(Formula w) => Call("length",w);
    private static Formula Occurrence(Formula w) => Ex(And(Call("member",I("omega"),I("X")),Call("Occurs",I("omega"),w)),B("omega",Config));
    private static Formula Binary(Formula theta) => Pow(D(2),Neg(theta));
    private static Formula Term(Formula theta, Formula w) => Call("wordTerm",theta,w);
    private static Formula Z(Formula k, Formula theta) => Call("partitionSum",I("X"),k,theta);
    private static Formula U(Formula theta, Formula k) => Call("logPartition",I("X"),theta,k);
    private static Formula Q(Formula theta, Formula k) => Div(U(theta,k),R(k));
    private static Formula P(Formula theta) => Call("pressure",I("X"),theta);
    private static Formula Rate => Call("weightedFactorRate",I("X"));
    private static Formula FactorTerm => Mul(R(Call("factorCount",I("X"),I("T"))),Pow(Binary(I("theta")),I("T")));
    private static Formula Whole => Tsum("w",Words,ER(Term(I("theta"),Val(I("w")))));
    private static Formula Source(Formula p) => All(p,B("X",Language));
    private static Formula NonemptySource(Formula p) => Source(Imp(Occupied,p));
    private static Formula Theta(Formula p) => All(p,B("theta",Real));
    private static Formula Infimum => Call("sInf",Call("image",Lam("k",Nat,Q(I("theta"),I("k"))),Call("Ici",D(1))));
    private static Formula Slopes(Formula p, Formula q) => And(Le(Sub(p,Mul(D(2,0),I("a"))),q),Le(q,Sub(p,Mul(D(6),I("a")))));
    private static DocumentBlock Node(string name, Formula statement, string prose, DescribeRole role=DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("fib-weighted-pressure-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
        H(name.Replace('_',' ')),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual occurring-word pressure has the original sparse weighted factor rate as its unique zero.",
        H("Weighted pressure of the actual bilateral language"),Blocks(
        Paragraph(Text("For the nonempty binary bilateral subshift X of source lemma 62.16, every word is indexed once regardless of how many configurations or positions realize it. The letters u and c have weights six and twenty. The formulas also hold for arbitrary nonempty sets of bilateral configurations; closedness and shift invariance of the source subshift are retained without a graph, a run cap, or a positive-entropy requirement.")),
        Node("OccurringWord",Source(Equal(Words,Call("subtype",Lam("w",Word,Occurrence(I("w")))))),
            "An element consists of the finite letter list and the proposition that it occurs in some configuration of X. Proofs and occurrence positions do not supply extra indices.",DescribeRole.Definition),
        Node("LengthDictionary",Source(All(Equal(Dictionary(I("k")),Call("subtype",Lam("w",Word,
            And(Occurrence(I("w")),Equal(Length(I("w")),I("k")))))),B("k",Nat))),
            "The dictionary contains exactly the actual occurring words of length k, including the empty word when k is zero.",DescribeRole.Definition),
        Node("lengthDictionary_finite",Source(All(Call("Finite",Dictionary(I("k"))),B("k",Nat))),
            "Indexing a length-k list by Fin k injects the dictionary into the finite set of binary k-tuples."),
        Node("length_dictionary_nonempty",NonemptySource(All(Call("Nonempty",Dictionary(I("k"))),B("k",Nat))),
            "Restrict any configuration of X to positions zero through k minus one. This gives an occurring word at every length, including zero."),
        Node("wordTerm",All(Equal(Term(I("theta"),I("w")),Pow(Binary(I("theta")),Weight(I("w")))),B("theta",Real),B("w",Word)),
            "The natural-power monomial is exactly two to minus theta times the original total word weight.",DescribeRole.Definition),
        Node("partitionSum",Source(Theta(All(Equal(Z(I("k"),I("theta")),Sum("w",Dictionary(I("k")),Term(I("theta"),Val(I("w"))))),B("k",Nat)))),
            "The real partition sum is finite and counts each actual word once.",DescribeRole.Definition),
        Node("logPartition",Source(Theta(All(Equal(U(I("theta"),I("k")),Call("logb",D(2),Z(I("k"),I("theta")))),B("k",Nat)))),
            "The logarithm is in base two.",DescribeRole.Definition),
        Node("pressure",Source(Theta(Equal(P(I("theta")),Infimum))),
            "The pressure is the infimum of all positive-length logarithmic quotients. Length zero is excluded from this infimum.",DescribeRole.Definition),
        Node("partition_positive",NonemptySource(Theta(All(Lt(D(0),Z(I("k"),I("theta"))),B("k",Nat)))),
            "Every monomial is strictly positive and every length dictionary is nonempty."),
        Node("splitWord",Source(All(Call("hasType",Call("splitWord",I("X"),I("k"),I("j")),
            Fn(Dictionary(Add(I("k"),I("j"))),Call("Product",Dictionary(I("k")),Dictionary(I("j"))))),B("k",Nat),B("j",Nat))),
            "Take the first k letters and drop those k letters. Both pieces occur in the same realizing configuration, at the original position and at its translate by k.",DescribeRole.Definition),
        Node("split_word_injective",Source(All(Call("Injective",Call("splitWord",I("X"),I("k"),I("j"))),B("k",Nat),B("j",Nat))),
            "Appending the two pieces recovers the original word. No pair is counted more than once."),
        Node("partition_submultiplicative",Source(Theta(All(Le(Z(Add(I("k"),I("j")),I("theta")),Mul(Z(I("k"),I("theta")),Z(I("j"),I("theta")))),B("k",Nat),B("j",Nat)))),
            "Weight is additive under append. The split injection embeds the summands into the product dictionary, whose remaining monomials are nonnegative."),
        Node("log_partition_subadditive",NonemptySource(Theta(Call("Subadditive",Lam("k",Nat,U(I("theta"),I("k")))))),
            "The positive partition sums allow the submultiplicative inequality to pass to their actual logarithms."),
        Node("partition_lower_bound",NonemptySource(Theta(All(Le(Pow(D(2),Mul(Mul(Neg(D(2,0)),Call("abs",I("theta"))),R(I("k")))),Z(I("k"),I("theta"))),B("k",Nat)))),
            "One occurring word, with weight at most twenty times its length, gives this lower bound uniformly in X and k for every real theta."),
        Node("log_quotient_lower_bound",NonemptySource(Theta(All(Le(Mul(Neg(D(2,0)),Call("abs",I("theta"))),Q(I("theta"),I("k"))),B("k",Nat)))),
            "The logarithmic quotient is bounded below by minus twenty times the absolute value of theta. At k equal to zero the real quotient is zero, so the same bound remains valid."),
        Node("pressure_tendsto",NonemptySource(Theta(Call("Tendsto",Lam("k",Nat,Q(I("theta"),I("k"))),I("atTop"),Call("nhds",P(I("theta")))))),
            "Fekete's lemma applies to the derived subadditive logarithms and the proved uniform quotient lower bound. Its limit is the exact infimum over every k at least one."),
        Node("partition_shift_bounds",Source(Theta(All(Imp(Le(D(0),I("a")),And(
            Le(Mul(Pow(D(2),Mul(Mul(Neg(D(2,0)),I("a")),R(I("k")))),Z(I("k"),I("theta"))),Z(I("k"),Add(I("theta"),I("a")))),
            Le(Z(I("k"),Add(I("theta"),I("a"))),Mul(Pow(D(2),Mul(Mul(Neg(D(6)),I("a")),R(I("k")))),Z(I("k"),I("theta")))))),B("k",Nat),B("a",Real)))),
            "For a nonnegative shift a, each exponent uses the same word weight between six k and twenty k. Summing preserves both bounds."),
        Node("pressure_shift_bounds",NonemptySource(Theta(All(Imp(Le(D(0),I("a")),Slopes(P(I("theta")),P(Add(I("theta"),I("a"))))),B("a",Real)))),
            "Divide the logarithmic partition bounds by positive k and pass to the proved limits. The source's slopes are minus twenty and minus six, with the zero-shift case included."),
        Node("pressure_lipschitz",NonemptySource(Call("LipschitzWith",D(2,0),Lam("theta",Real,P(I("theta"))))),
            "The two slope bounds give a global Lipschitz constant of twenty, hence continuity on the whole real line."),
        Node("pressure_strictAnti",NonemptySource(Call("StrictAnti",Lam("theta",Real,P(I("theta"))))),
            "The upper slope bound decreases pressure strictly whenever the exponent increases."),
        Node("pressure_zero_nonneg",NonemptySource(Le(D(0),P(D(0)))),
            "At theta zero every word contributes one. Nonemptiness makes every logarithmic quotient nonnegative; zero entropy is allowed."),
        Node("pressure_unique_zero",NonemptySource(Call("existsUnique",Lam("eta",Real,And(Le(D(0),I("eta")),Equal(P(I("eta")),D(0)))))),
            "Continuity, P at zero nonnegative, and the literal upper slope give a nonnegative zero by the intermediate value theorem. Strict decrease makes it unique."),
        Node("whole_series_regrouping",Source(Theta(And(Equal(Whole,Tsum("k",Nat,ER(Z(I("k"),I("theta"))))),Equal(Whole,Tsum("T",Nat,ER(FactorTerm)))))),
            "Partition the exact occurring-word index by length and then by original weight. The length fiber is the finite length dictionary; the weight fiber is the original finite FactorDictionary and contributes factorCount times the constant monomial. Both ENNReal equalities include infinity."),
        Node("whole_series_finiteness",Source(Theta(And(
            Iff(Summable("k",Nat,Z(I("k"),I("theta"))),Lt(Whole,I("infinity"))),
            Iff(Summable("T",Nat,FactorTerm),Lt(Whole,I("infinity")))))),
            "The meaningful ENNReal condition is that the whole sum is less than infinity. It is equivalent to real summability for both regroupings. Bare ENNReal Summable imposes no finiteness condition."),
        Node("whole_series_nonpositive",NonemptySource(Theta(Imp(Le(I("theta"),D(0)),Equal(Whole,I("infinity"))))),
            "Actual words of every length give an injection of the natural numbers into the occurring-word index. At nonpositive theta all their monomials are at least one, so the whole sum is infinite."),
        Node("negative_pressure_summable",NonemptySource(Theta(Imp(Lt(P(I("theta")),D(0)),Summable("k",Nat,Z(I("k"),I("theta")))))),
            "A negative limit of the logarithmic quotients gives an eventual geometric majorant of ratio less than one."),
        Node("pressure_zero_iff_rate",NonemptySource(Theta(Iff(Equal(P(I("theta")),D(0)),Equal(I("theta"),Rate)))),
            "The original factor_rate_convergence criterion applies at positive exponents through the exact whole-series correspondence. Nonpositive exponents diverge. If the zero and the sparse max-one weightedFactorRate differed, an exponent strictly between them would contradict either geometric convergence or pressure strictness. Unsupported weights stay in the original count sequence. No convergence claim at the zero is used."),
        Paragraph(Text("These formulas establish source lemma 62.16. Nested compact-language stabilization and pressure limits, same-reset actual and bilateral codebooks, actual-list count bridges, and all-even source-length asymptotics require their respective additional constructions.")))));
}
