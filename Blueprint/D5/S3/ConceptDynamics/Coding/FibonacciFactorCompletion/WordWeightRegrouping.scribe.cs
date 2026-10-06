using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class WordWeightRegroupingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Lam(string n, Formula t, Formula p) => new Formula.Sequence(p,I(n),t);
    private static Formula Sum(string n, Formula t, Formula p) => Call("sum",Lam(n,t,p));
    private static Formula Tsum(string n, Formula t, Formula p) => Call("tsum",Lam(n,t,p));
    private static Formula Summable(string n, Formula t, Formula p) => Call("Summable",Lam(n,t,p));
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Power(Formula a, Formula b) => Call("power",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Core => Call("CorePathWitnessDictionary",I("side"),I("n"),I("K"),I("d"),I("T"));
    private static Formula Retained => Call("RetainedPathDictionary",I("side"),I("n"),I("K"),I("d"),I("T"));
    private static Formula Vertex => Call("CoreVertex",I("side"),I("n"),I("K"),I("d"));
    private static Formula Language => Call("MemoryLanguage",I("side"),I("n"),I("K"),I("d"));
    private static Formula PathTerm => Mul(Call("toReal",Call("NatCard",Retained)),Power(I("z"),I("T")));
    private static Formula FactorTerm(Formula x, Formula z) => Mul(Call("toReal",Call("factorCount",x,I("T"))),Power(z,I("T")));
    private static Formula Radius(Formula z) => Call("weightedRadius",I("side"),I("n"),I("K"),I("d"),z);
    private static Formula Rate(Formula x) => Call("weightedFactorRate",x);
    private static Formula BinaryZ => Power(D(2),Call("negate",I("s")));
    private static Formula PathMass()
    {
        var choices=Fn(Call("Fin",I("k")),Call("Product",I("CuLetter"),Vertex));
        return Sum("v",Vertex,Sum("choices",choices,Call("coreMonomial",I("side"),I("K"),I("d"),I("z"),I("k"),I("v"),I("choices"))));
    }
    private static Formula Base(Formula p) => All(Imp(And(Lt(D(0),I("K")),Le(I("K"),I("n"))),p),B("side",I("MemorySide")),B("n",Nat),B("K",Nat),B("d",Real),B("T",Nat));
    private static Formula BaseZ(Formula p) => All(Imp(And(Lt(D(0),I("K")),Le(I("K"),I("n"))),p),B("side",I("MemorySide")),B("n",Nat),B("K",Nat),B("d",Real),B("z",Real),B("T",Nat));
    private static Formula Series(Formula p) => All(Imp(And(Lt(D(0),I("K")),Le(I("K"),I("n")),Le(D(0),I("z"))),p),B("side",I("MemorySide")),B("n",Nat),B("K",Nat),B("d",Real),B("z",Real));
    private static Formula Regrouping() => Series(And(
        Iff(Summable("k",Nat,PathMass()),Summable("T",Nat,PathTerm)),
        Equal(Tsum("k",Nat,PathMass()),Tsum("T",Nat,PathTerm))));
    private static Formula Convergence()
    {
        var term=FactorTerm(I("X"),BinaryZ);
        var conclusion=And(Imp(Lt(Rate(I("X")),I("s")),Summable("T",Nat,term)),
            Imp(Summable("T",Nat,term),Le(Rate(I("X")),I("s"))));
        return All(Imp(Lt(D(0),I("s")),conclusion),B("X",Call("Set",Fn(I("Int"),I("CuLetter")))),B("s",Real));
    }
    private static Formula Abscissa()
    {
        var set=Call("setOf",Lam("s",Real,And(Lt(D(0),I("s")),Lt(Radius(BinaryZ),D(1)))));
        return All(Imp(And(Lt(D(0),I("K")),Le(I("K"),I("n"))),Equal(Rate(Language),Call("sInf",set))),
            B("side",I("MemorySide")),B("n",Nat),B("K",Nat),B("d",Real));
    }
    private static DocumentBlock Node(string name, Formula statement, string prose) => Describe.Lean(
        DescribeId.Create("fib-word-regrouping-"+name.Replace('_','-')),DeclarationHandle.Create(Prefix+name),
        H(name.Replace('_',' ')),StatementSource.FromAuthor(statement),AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual retained path monomials regroup by original wordWeight, and the original max-one weighted factor rate equals their spectral convergence abscissa.",
        H("Actual word-weight regrouping and rate abscissa"),Blocks(
        Paragraph(Text("All paths use the original finite-past memories and both original guard conventions. The c and u labels retain weights twenty and six, including parallel labels with coincident endpoints. Empty walks, empty retained carriers, reducible graphs and walks across transient bridges remain in the quantified scope.")),
        Node("core_path_witness_dictionary_equiv",Base(Call("Nonempty",Call("Equiv",Core,Retained))),
            "The recursive constructor rebuilds the actual successive memory vertices of every retained walk. The initial vertex and letter list determine the CorePath choices uniquely. Destructing the dependent sigma and subtype values proves equality without an unchecked cast."),
        Node("core_path_witness_dictionary_card",Base(Equal(Call("NatCard",Core),Call("NatCard",Retained))),
            "The two actual dictionaries have equal cardinality. This auxiliary equality is used in the weighted fibre sum."),
        Node("actual_weight_regrouping",BaseZ(Equal(Tsum("x",Core,Power(I("z"),I("T"))),PathTerm)),
            "For one fixed weight T and any real z, the finite witness dictionary sums the constant z to T. This auxiliary formula supplies each fibre of the whole-series reindexing."),
        Node("actual_monomial_series_regrouping",Regrouping(),
            "For nonnegative z, the complete series over letter length k has the same summability and the same real tsum as the series over actual word weight T. Invalid choices contribute zero and are removed by their support. Genuine paths are partitioned by their original total weight; the constructed dictionary equivalence makes each finite fibre sum the retained path count times z to T. The equality includes divergent series, for which both real tsums are zero; summability is stated separately."),
        Node("actual_factor_path_summability",Series(Iff(Summable("T",Nat,PathTerm),Summable("T",Nat,FactorTerm(Language,I("z"))))),
            "At each actual weight the existing original sandwich bounds the factor count by the path count, and the path count by two to n times the factor count. Nonnegative comparison therefore transfers convergence in both directions with a constant independent of T."),
        Node("original_factor_series_boundary",Series(Iff(Summable("T",Nat,FactorTerm(Language,I("z"))),Lt(Radius(I("z")),D(1)))),
            "The original factor power series converges exactly when the original weighted adjacency has spectral radius below one. The result follows through the complete actual path regrouping and the existing spectral path-series supplier, without a supplied growth identity."),
        Node("factor_rate_convergence",Convergence(),
            "For every bilateral factor language and every positive real s, the original max-one limsup rate below s implies convergence at z equal to two to minus s, and convergence implies that the rate is at most s. The forward proof uses an eventual geometric majorant strictly between the rate and s. The reverse proof uses terms tending to zero and keeps the max-one convention, so unsupported sparse weights cause no logarithm of zero. No claim about convergence exactly at a generic rate is made."),
        Node("original_weighted_rate_abscissa",Abscissa(),
            "For both actual memory sides and every positive K at most n, the original weightedFactorRate is the infimum of the positive binary exponents whose actual weighted adjacency has radius below one. The set is nonempty and bounded below. This identifies the actual max-one, sparse-weight limsup with the original spectral convergence abscissa."),
        Paragraph(Text("The original n at least K at least two and interior transition-budget regime remains the scope of the interior-root target. Existence and uniqueness of that root, strict spectral increase, its identification as the abscissa parameter, lower/upper nesting, auxiliary bilateral/SFT inclusions and intersection, graph margins, graph-rate convergence, eventual even allN asymptotics, canonical containing paths, storage/decoder and optimum conclusions remain separate obligations.")))));
}
