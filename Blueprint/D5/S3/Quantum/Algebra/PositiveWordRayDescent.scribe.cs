using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PositiveWordRayDescentDocument : IScribeDocumentDefinition
{
    private static Formula R = F.Id("R"), G = F.Id("G"), L = F.Id("L");
    private static Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), f = F.Id("f");
    private static Formula P = F.Id("P"), q = F.Id("q"), r = F.Id("r"), x = F.Id("x");
    private static Formula eps = F.Id("epsilon"), delta = F.Id("delta"), s = F.Id("s");
    private static Formula W = Call("List", Call("Fin", D(1,1)));
    private static Formula empty = Call("nil");
    private static Formula row(Formula w) => Call("row", L, w);
    private static Formula ray(Formula w) => Call("ray", G, w);
    private static Formula prob(Formula w) => Call("probability", L, w);
    private static Formula append(Formula u, Formula v) => Call("append", u, v);
    private static Formula d(Formula u, Formula v) => Call("dist", u, v);
    private static Formula inv(Formula w) => Call("inverseWord", w);
    private static Formula all(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Colon, type, Comma, Esc, body);
    private static Formula premise(Formula body, bool dense = false, bool compact = false,
        bool statistics = false, bool ready = false) => Disp(Seq(
        all(R,Call("Type"),all(L,Call("Law"),all(G,Call("Geometry",R),Seq(
        Call("MetricSpace",R),
        dense ? Seq(Sp,Land,Sp,Call("DenseRange",Call("ray",G))) : Seq(),
        compact ? Seq(Sp,Land,Sp,Call("CompactSpace",R)) : Seq(),
        statistics ? Seq(Sp,Land,Sp,Call("Rten",L)) : Seq(),
        ready ? Seq(Sp,Land,Sp,Call("ReadyReturn",L,G)) : Seq(),
        Sp,Rightarrow,Sp,body))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive statistical return and sequential ready return yield a continuous full-row response.",
        H("Positive Words, Ready Return and Continuous Ray Descent"),
        Paragraph(Text("The word domain W is List(Fin 11), with chronological concatenation: act(a++b,P)=act(b,act(a,P)). A Law is an arbitrary real function p on all these words with 0<=p(a)<=1. Coordinates are Option W with the discrete topology. The none coordinate is star and is always one; some [] is the empty terminal future and equals p(a). The row x(a) is the bounded continuous function (1,(p(a++f)) for every f in W), with its full supremum norm. V is the real algebraic span of all rows, and Vhat=closedSpan is its norm closure in this Banach space. No dimension or closedness hypothesis on V occurs.")),
        Paragraph(Text("Geometry R means a metric space R, eleven maps gate(j):R->R, each an isometry with tenth iterate equal to the identity at every point, and one ready point. act is chronological iteration and ray(a)=act(a,ready). Density means DenseRange ray on this same metric space. Compactness is required only in the backward represented-statistics argument. Rten is the statistical equality p(a++j^10++f)=p(a++f) for every a,j,f. ReadyReturn is sequential convergence of full rows to the empty row whenever a sequence of actual word rays converges to the ready ray; it is not pointwise convergence at each fixed future.")),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-word-row-return"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PositiveWordRayDescent.row_return_transport"),
                H("The same positive inverse transports both rows"),
                StatementSource.FromAuthor(Disp(all(L,Call("Law"),Seq(
                    Call("Rten",L),Sp,Rightarrow,Sp,all(a,W,all(b,W,Seq(
                    d(row(a),row(b)),Eq,d(row(append(a,inv(b))),row(empty))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("inverseWord reverses the address order and replaces each address by nine positive copies. Statistical Rten cancels b++inverseWord(b) between every prefix and every future. Appending any word is a contraction on row differences because it restricts the future coordinates. Appending its positive inverse recovers the original difference, so the contraction is an isometry on these row pairs. In particular x(b++inverseWord(b))=x([]), and simultaneous transport gives the displayed identity. Geometry plays no part in this statistical proof. This identity does not equate program histories or provide a physical inverse service."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-word-uniform-fibers"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PositiveWordRayDescent.uniform_rows_and_fibers"),
                H("Sequential return controls all pairs and noninjective fibers"),
                StatementSource.FromAuthor(premise(Seq(
                    Open,all(eps,Call("Real"),Seq(D(0),Lt,eps,Sp,Rightarrow,Sp,
                        Exists,Sp,delta,Colon,Call("Real"),Comma,Esc,D(0),Lt,delta,Sp,Land,Sp,
                        all(a,W,all(b,W,Seq(d(ray(a),ray(b)),Lt,delta,Sp,Rightarrow,Sp,
                            d(row(a),row(b)),Lt,eps))))),Close,Sp,Land,Sp,
                    all(a,W,all(b,W,Seq(ray(a),Eq,ray(b),Sp,Rightarrow,Sp,row(a),Eq,row(b))))),
                    statistics:true,ready:true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If an epsilon bound failed at ready, choose a violating actual word c(n) whose ray distance is less than 1/(n+1). These rays converge to ready, while their full row distances stay at least epsilon, contradicting the sequential premise. For arbitrary a,b, append inverseWord(b) to both. Statistical transport preserves their row distance. The same positive word acts isometrically on both rays and returns ray(b) to ready, by the independent tenth-order geometry. Thus one ready bound controls all actual pairs. Applying every positive epsilon to an equal-ray pair makes its row distance zero. The word map is never assumed injective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-word-continuous-descent"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PositiveWordRayDescent.continuous_descent"),
                H("Unique full-row extension into the closed span"),
                StatementSource.FromAuthor(DescentFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists a unique continuous Phi:R->Vhat satisfying all four conditions: Phi(ray(a))=x(a) for every word; Phi(P)(none)=1; every Phi(P)(some f) belongs to [0,1]; and Phi(P)(some f)=Phi(act(f,P))(some []) for every P and every original future f. Descent in the formula denotes exactly this conjunction. In particular q(P)=Phi(P)(some []) is continuous, takes values in [0,1], and represents p at every actual ray.")),
                    Paragraph(Text("First apply uniform_rows_and_fibers. Choose a representing word only on range(ray); fiber constancy makes the chosen row independent of that word, and the pair estimate makes this map uniformly continuous in the inherited ray metric. Mathlib Dense.uniformContinuous_extend extends it into the complete bounded-row space. The closed span contains every row, so dense induction places every extension value in Vhat; the map is then lifted into that closed subtype. Continuous coordinate evaluation extends normalization and bounds. For each f, both coordinate evaluation and evaluation after act(f) are continuous and agree on the dense actual rays, which proves the full future formula. The same dense equalizer proves uniqueness. The raw word-to-ray map need not be a uniform embedding."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-word-represented-statistics"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PositiveWordRayDescent.represented_statistics"),
                H("A continuous representation supplies both statistical premises"),
                StatementSource.FromAuthor(premise(all(q,Call("ContinuousMap",R,Call("Icc",D(0),D(1))),
                    Seq(Open,all(a,W,Seq(Call("q",ray(a)),Eq,prob(a))),Close,Sp,Rightarrow,Sp,
                        Call("Rten",L),Sp,Land,Sp,Call("ReadyReturn",L,G))),compact:true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume q is a continuous [0,1]-valued response representing all actual p(a). Compactness gives uniform continuity of its real coordinate. A half-epsilon bound applies simultaneously after every future because act(f) is an isometry. BoundedContinuousFunction.dist_le gives a full supremum bound, then the strict half-epsilon margin proves ReadyReturn. The same assumed representation transfers the geometric tenth-order identity to every statistical prefix/future equality. Gate order by itself is not a premise about an unknown terminal law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-word-response-equivalence"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PositiveWordRayDescent.ready_return_iff_unique_response"),
                H("Capacity-free return and a unique continuous response are equivalent"),
                StatementSource.FromAuthor(ResponseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For compact R and dense actual ready orbit, Rten and ReadyReturn hold if and only if there exists exactly one continuous q:R->[0,1] representing all p(a). The forward proof consumes continuous_descent and evaluates some []; the backward proof consumes represented_statistics. Equality on the same dense rays gives uniqueness. The constant law p=1/3 has star coordinate one and empty-future coordinate 1/3, so the two coordinates cannot be interchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-word-three-moduli"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PositiveWordRayDescent.three_moduli_equal"),
                H("Return, pair and scalar suprema agree exactly"),
                StatementSource.FromAuthor(ModuliFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s>=0, returnErrors consists of distances Delta(c,[]) with ray distance at most s; pairErrors consists of Delta(a,b) under the pair ray-distance constraint; scalarErrors consists of |p(a)-p(b)| under that same constraint. All three sets contain zero and are bounded above by one. Their real suprema are equal, and the return supremum lies in [0,1]. No supremum is assumed attained. This includes every source value 0<=s<=1 and the endpoint s=0.")),
                    Paragraph(Text("Pair candidates transport to return candidates by the same reverse-nine word, preserving the constraint. Return candidates are pair candidates with the second word empty. Empty-future evaluation bounds scalar error by row error. Conversely every common future gives a scalar candidate at the same ray distance, by isometry; bounding every coordinate by the scalar supremum bounds the whole row distance. The proof uses le_csSup and csSup_le only after explicit nonemptiness and boundedness. ReadyReturn and compactness are unnecessary for this equality."))), DescribeRole.Theorem)),
        H("Original native application and remaining geometric correspondence"),
        Paragraph(Text("The intended source is VII24.1-25.1 with III150.1 geometry and VII10.1/17.1 conventions. Its native specialization is R=the pure rays of the original V12^1, complex dimension 89, with d(P,Q)=operatorNorm(P-Q); gate(j) is conjugation by the same original K_j; ready is P_(e0) with e0=R0 v; p(a) is the unknown actual event probability for A={b1=1}. Every eleven-address positive history and every terminal future is retained. The 26-dimensional J(H tensor C^2) code and all 63 complementary dimensions, J itself, the phase/address convention, ordinary causal normalization and original ideal, finite-supply, reliability and cost contracts keep their original meanings. Geometry and density are inputs from the paper, never deductions from statistical Rten.")),
        Paragraph(Text("This metric-geometry theorem does not yet instantiate that original carrier. WeightedLegalPathTemperleyLieb.LegalPath/pathProjection and WeightedPathArtinRepresentation.rho/rhoUnit supply reusable path and generator algebra, but a typed equality with the original V12^1, all eleven normalized gates, e0, J and Q is still required. RankOneContextCommutator.IsNormalizedRankOneProjection is algebraic; it does not provide the compact operator-norm ray space. The further obligations are the faithful normalized-projector metric/compactness bridge, original gate unitarity and tenth-order phase specialization, and DenseRange of the same actual ready rays while preserving the full PU(89) density assumption. No arbitrary Fin 89 matrix family or different NativeProtocol is identified with those native objects.")),
        Paragraph(Text("The intended path parameters are the two labels Bool, with true denoting vacuum, adjacency excluding two consecutive true labels, d(true)=1, d(false)=phi and delta=phi. The n=12 true-to-true block has the literal boundary form (1,0,b1,...,b9,0,1), with no adjacent occupied internal bits. The required source correspondence sends this full path block to the original basis; the original extra right boundary bit remains fixed at zero. This parameter assignment specifies a concrete correspondence to prove, not a completed Lean equivalence. With A=exp(2*pi*i/5), the original phase convention calls for K_j=-rho_j on that same block; verifying the parameter equation, projection entries and this phase identity is part of the unpaid native gate bridge.")),
        Paragraph(Text("The result supplies the analytic return/descent predecessor needed by the closed native consumer in Quantum VI89.9. The entire fixed native theorem remains conditional on those native bridges. The full-span linear operator formulation of VII24.2 is separate from the row-distance transport proved here. No Born classification, predictive capacity, finite separating future family, physical inverse availability or change to the original program domain follows from this unit. Generic bounded-function construction, coordinate evaluation and dense extension are direct Mathlib applications; the new inference is the positive-word passage from sequential ready return to global row consistency and its continuous descent consumer."))));

    private static Formula DescentFormula() => premise(Seq(
        Exists,Sp,Phi,Colon,Call("ContinuousMap",R,Call("closedSpan",L)),Comma,Esc,
        Call("Descent",L,G,Phi),Sp,Land,Sp,
        all(x,Call("ContinuousMap",R,Call("closedSpan",L)),Seq(
            Call("Descent",L,G,x),Sp,Rightarrow,Sp,x,Eq,Phi))),dense:true,statistics:true,ready:true);

    private static Formula ResponseFormula() => premise(Seq(
        Open,Call("Rten",L),Sp,Land,Sp,Call("ReadyReturn",L,G),Close,Sp,Leftrightarrow,Sp,
        Exists,Sp,q,Colon,Call("ContinuousMap",R,Call("Icc",D(0),D(1))),Comma,Esc,
        Open,all(a,W,Seq(Call("q",ray(a)),Eq,prob(a))),Close,Sp,Land,Sp,
        all(r,Call("ContinuousMap",R,Call("Icc",D(0),D(1))),Seq(
            Open,all(a,W,Seq(Call("r",ray(a)),Eq,prob(a))),Close,Sp,Rightarrow,Sp,r,Eq,q))),
        dense:true,compact:true);

    private static Formula ModuliFormula() => premise(all(s,Call("Real"),Seq(
        D(0),Le,s,Sp,Rightarrow,Sp,
        Call("sSup",Call("returnErrors",L,G,s)),Eq,Call("sSup",Call("pairErrors",L,G,s)),Sp,Land,Sp,
        Call("sSup",Call("pairErrors",L,G,s)),Eq,Call("sSup",Call("scalarErrors",L,G,s)),Sp,Land,Sp,
        Call("Member",Call("sSup",Call("returnErrors",L,G,s)),Call("Icc",D(0),D(1))))),statistics:true);
}
