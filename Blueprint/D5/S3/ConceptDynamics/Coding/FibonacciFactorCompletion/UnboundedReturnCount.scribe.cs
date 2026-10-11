using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class UnboundedReturnCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula If(Formula p, Formula a, Formula b) => Call("ifThenElse",p,a,b);
    private static Formula Card(Formula a) => Call("card",a);
    private static Formula Half(Formula a) => Call("halfWeight",a);
    private static Formula Words(Formula a) => Call("middleWords",a);
    private static Formula Count(Formula a) => Call("returnCount",a);
    private static Formula Cast(Formula a) => Call("toReal",a);
    private static Formula Lam(string n, Formula t, Formula p) => F.Seq(Open,I(n),Sp,Colon,Sp,t,Sp,Mapsto,Sp,p,Close);
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Word => Call("List",I("CuLetter"));
    private static Formula Lists => Call("List",I("Return"));
    private static Formula Empty => Call("nil",I("CuLetter"));
    private static Formula Alpha => I("alphaInfinity");
    private static Formula Log(Formula n) => Call("logb",D(2),Cast(Count(n)));
    private static Formula Term(int delay, Formula n) => delay == 3
        ? If(Le(D(3),n),Count(Sub(n,D(3))),D(0))
        : If(Le(D(1,0),n),Count(Sub(n,D(1,0))),D(0));
    private static DocumentBlock Node(string name, Formula p, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("fib-unbounded-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
            H(name.Replace('_',' ')),StatementSource.FromAuthor(Disp(p)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create()
    {
        var n=I("n"); var w=I("w"); var x=I("x"); var xs=I("xs");
        var root=And(Lt(D(0),x),Lt(x,D(1)),Equal(Add(Pow(x,D(3)),Pow(x,D(1,0))),D(1)));
        var fiber=Call("subtype",Lam("xs",Lists,And(Call("ne",xs,Call("nil",I("Return"))),
            Equal(Call("listWeight",xs),Mul(D(2),n)))));
        var delayedWords=Call("union",If(Equal(n,D(0)),Call("singleton",Empty),Call("emptyFinset",Word)),
            Call("union",If(Le(D(3),n),Call("image",Lam("w",Word,Call("cons",I("u"),w)),Words(Sub(n,D(3)))),Call("emptyFinset",Word)),
            If(Le(D(1,0),n),Call("image",Lam("w",Word,Call("cons",I("c"),w)),Words(Sub(n,D(1,0)))),Call("emptyFinset",Word))));
        var window=And(All(Le(Mul(Cast(Count(n)),Pow(x,n)),Pow(x,D(1,3))),B("n",Nat)),
            All(Imp(Le(D(3,1),n),Le(Pow(x,D(4,0)),Mul(Cast(Count(n)),Pow(x,n)))),B("n",Nat)));
        var logBounds=And(Lt(D(0),Alpha),All(Imp(Le(D(3,1),n),And(Lt(D(0),Cast(Count(n))),
            Le(Sub(Mul(Mul(D(2),Alpha),Cast(n)),Mul(D(8,0),Alpha)),Log(n)),
            Le(Log(n),Sub(Mul(Mul(D(2),Alpha),Cast(n)),Mul(D(2,6),Alpha))))),B("n",Nat)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Positive return lists are in bijection with their weighted binary middle words.",H("Unbounded positive return counts"),Blocks(
            Paragraph(Text("A return has positive integer exponents m and r and contributes six m plus twenty r original windows. Execution order reverses the external source order: the nonempty execution word has the form c W u, corresponding to U W C externally. The existing maximal-run parser identifies every such word with exactly one positive return list. No bound on either exponent, block boundaries supplied to a decoder, or finite-memory language is assumed.")),
            Node("halfWeight",And(Equal(Half(Empty),D(0)),All(Equal(Half(Call("cons",I("c"),w)),Add(D(1,0),Half(w))),B("w",Word)),
                All(Equal(Half(Call("cons",I("u"),w)),Add(D(3),Half(w))),B("w",Word))),
                "The half length gives weight ten to c and three to u.",DescribeRole.Definition),
            Node("middleWords",All(Equal(Words(n),delayedWords),B("n",Nat)),
                "The finite set enumerates exactly the binary words with the specified half length. Its three branches distinguish the empty word and the first letter.",DescribeRole.Definition),
            Node("ReturnFiber",All(Equal(Call("ReturnFiber",n),fiber),B("n",Nat)),
                "Only nonempty actual positive return lists with original length twice n belong to this fiber.",DescribeRole.Definition),
            Node("returnCount",All(Equal(Count(n),Call("NatCard",Call("ReturnFiber",n))),B("n",Nat)),
                "The count is the cardinality of the original list fiber, independently of its word enumeration.",DescribeRole.Definition),
            Node("actual_count_middle",All(And(Call("Finite",Call("ReturnFiber",n)),Equal(Count(n),
                If(Le(D(1,3),n),Card(Words(Sub(n,D(1,3)))),D(0)))),B("n",Nat)),
                "The forced endpoints have half length thirteen. Removing them preserves weight and gives the finite middle-word dictionary; the inverse uses complete run decomposition."),
            Node("actual_count_recurrence",All(Equal(Count(n),Add(Add(Term(3,n),Term(10,n)),If(Equal(n,D(1,3)),D(1),D(0)))),B("n",Nat)),
                "The disjoint first-middle-letter partition subtracts three or ten. The empty middle contributes the pulse at thirteen. The guards implement zero extension, including indices below a delay."),
            Node("actual_count_support",All(Iff(Lt(D(0),Count(n)),Ex(Equal(n,Add(Add(D(1,3),Mul(D(3),I("a"))),Mul(D(1,0),I("b")))),B("a",Nat),B("b",Nat))),B("n",Nat)),
                "The exact support is thirteen plus the semigroup generated by three and ten. In particular thirty is unsupported, whereas every index from thirty-one onward is supported."),
            Node("actual_count_window",All(Imp(root,window),B("x",Real)),
                "Scaling the recurrence by x to the index gives a convex combination. All indices thirty-one through forty are positive; the complete ten-index window has lower bound x to the fortieth power, which strong induction preserves. The upper bound starts at the pulse x to the thirteenth power."),
            Node("criticalX",Equal(I("criticalX"),Call("choose",Ex(root,B("x",Real)))),
                "The radius is chosen in the open unit interval where its third and tenth powers sum to one. Continuity and the endpoint values zero and two establish existence.",DescribeRole.Definition),
            Node("alphaInfinity",Equal(Alpha,Call("divide",Call("negate",Call("logb",D(2),I("criticalX"))),D(2))),
                "Dividing the negative base-two radius logarithm by two converts half lengths to original-window lengths.",DescribeRole.Definition),
            Node("actual_count_log_bounds",logBounds,
                "The count is positive from thirty-one onward. Its base-two logarithm lies between twice alpha times n minus eighty alpha and twice alpha times n minus twenty-six alpha. These fixed errors apply on the even original-length lattice."),
            Node("actual_even_rate",And(Call("IsBigO",I("atTop"),Lam("n",Nat,Sub(Log(n),Mul(Mul(D(2),Alpha),Cast(n)))),
                Call("constantFunction",Nat,Real,D(1))),
                Call("Tendsto",Lam("n",Nat,Call("divide",Log(n),Mul(D(2),Cast(n)))),I("atTop"),Call("nhds",Alpha))),
                "The logarithmic error is bounded by a constant. Dividing the two explicit logarithmic bounds by twice n gives the limit alpha along the even original-length lattice. This limit counts the specified actual family."),
            Paragraph(Text("The formal-series application of actual_count_recurrence takes F in the ring of formal power series over the integers, with coefficient n equal to returnCount n. The guards are precisely the zero coefficients below the two delays. Comparing coefficients gives (1-X^3-X^10)F=X^13. The denominator has constant coefficient one, so PowerSeries.invOfUnit supplies its inverse and F=X^13 invOfUnit(1-X^3-X^10,1). Quotient notation for this identity means multiplication by this formal unit inverse; no analytic evaluation or convergence is assumed.")),
            Paragraph(Text("For original return length k, define c_k as the cardinality of actual nonempty positive return lists xs with listWeight xs=k. The finite fibers of actual_count_middle and actual_list_weight_even give c_(2n)=returnCount n and c_(2n+1)=0. PowerSeries.expand by two sends F to T with these exact coefficients. It sends X^3 and X^10 to z^6 and z^20, and the pulse X^13 to z^26. Thus (1-z^6-z^20)T=z^26 and T=z^26 invOfUnit(1-z^6-z^20,1), or z^26/(1-z^6-z^20) in formal quotient notation. This counts nonempty lists; its constant coefficient is zero.")),
            Paragraph(Text("The empty list contributes one separately. paired_source_reconstruction identifies the original history length as 26+listWeight xs, while complete_execution_word_parser makes history .original injective on the actual lists. Consequently the coefficient at k of z^26(1+T) is exactly the number of these actual histories of length k. The empty list is the unique history at length 26, and every history has even length. The 26-window outer stem is distinct from the forced 26-window endpoints of a nonempty return list. The construction retains the same prescribed sources, execution reversal and fixed tails.")),
            Paragraph(Text("For every natural original return-length horizon N, let C(N) be the number of actual nonempty positive lists with listWeight xs at most N. The same even-weight map identifies this finite fiber with the disjoint union of ReturnFiber n over n in Fin(N/2+1). Hence C(N) is the sum of returnCount n for 0 through floor(N/2). Here N/2 is natural-number division, not real division. No odd-length fiber is included implicitly. Adding the empty list gives exactly 1+C(N), which matches the cumulative convention in source section 55.3 because returnCount 0 is zero.")),
            Paragraph(Text("Fix 0<x<1 with x^3+x^10=1, and put q=x inverse, A=x^40 and B=x^13 q/(q-1). These constants are positive and q>1. Applying actual_count_window to each fiber and the finite geometric-sum identity gives C(N) at most B q^floor(N/2) for every N. For N at least 62, the last fiber index is at least 31, so its lower window bound gives A q^floor(N/2) at most C(N). Thus for N at least 62, A q^floor(N/2) is at most 1+C(N), which is at most (B+1)q^floor(N/2). Since floor(N/2) lies between N/2-1 and N/2, the same bounds also give x^41 x^(-N/2) at most C(N), which is at most B x^(-N/2), for N at least 62; the exponents in this last expression are real powers. The lower bound has no positive all-N extension for nonempty lists: C(N)=0 when N<26. This finite initial range has no effect on the limiting rate.")),
            Paragraph(Text("Taking base-two logarithms of the positive bounds and dividing by N squeezes log2(C(N))/N between log2(A)/N plus floor(N/2)/N times log2(q), and the analogous expression with B. The floor ratio tends to one half, so the limit over all integer N is -log2(x)/2. The bound C(N) at most 1+C(N) at most 2C(N), valid from N=62, proves the same limit for the empty-list convention. Specializing x to criticalX gives alphaInfinity. The positive root is unique; zStar=sqrt(x) lies in (0,1), satisfies zStar^6+zStar^20=1, and -log2(zStar)=-log2(x)/2. These radius identities do not assert analytic convergence of the formal series.")),
            Paragraph(Text("For complete original histories with horizon N, the cumulative count is zero for N<26 and exactly 1+C(N-26) for N at least 26. For N at least 88 the displayed bounds apply with floor((N-26)/2). Composing the return-length rate with N minus 26 and multiplying by (N-26)/N proves that the history cumulative rate is also alphaInfinity over all integer horizons. Exact odd-length return counts remain zero; this all-integer statement concerns cumulative counts. The cumulative argument is not used to mix unequal histories in the equal-checkpoint storage injection.")),
            Paragraph(Text("These are consequences of the existing actual count, parity, parser and source-length declarations together with formal-series, finite geometric-sum and limit identities. They do not provide a decoder with free boundaries or positions. Section 55.2's endpoint sharpness, actual inner-slot costs, minimum family budget, lack of a uniform positive family margin and necessary subcritical cap require their own actual-source bridges. The universal representation of Definition 36.9 and the closed-observation online construction of section 33.13, including finite updates and complete linear workspace, control and counter accounting, remain separate obligations. Neither an attainable lower coefficient nor a globally optimal coefficient or matching optimal memory order follows from these applications.")))));
    }
}
