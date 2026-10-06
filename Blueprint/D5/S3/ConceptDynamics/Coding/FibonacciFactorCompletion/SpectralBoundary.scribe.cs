using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class SpectralBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Lambda(string n, Formula t, Formula p) => new Formula.Sequence(p,I(n),t);
    private static Formula Sum(string n, Formula t, Formula p) => Call("sum",Lambda(n,t,p));
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Radius(Formula n, Formula k, Formula z) => Call("weightedRadius",I("side"),n,k,I("d"),z);
    private static Formula Core => Call("CoreVertex",I("side"),I("n"),I("K"),I("d"));
    private static Formula Boundary()
    {
        var choices=Fn(Call("Fin",I("k")),Call("Product",I("CuLetter"),Core));
        var mass=Sum("v",Core,Sum("choices",choices,Call("coreMonomial",I("side"),I("K"),I("d"),I("z"),I("k"),I("v"),I("choices"))));
        return Disp(All(Imp(Le(D(0),I("z")),Iff(Call("Summable",Lambda("k",Nat,mass)),Lt(Radius(I("n"),I("K"),I("z")),D(1)))),B("side",I("MemorySide")),B("n",Nat),B("K",Nat),B("d",Real),B("z",Real)));
    }
    private static Formula ClosedRoot()
    {
        var language=Call("MemoryLanguage",I("side"),D(1),D(1),I("d"));
        var allU=Lambda("i",I("Int"),I("u"));
        var power=Call("power",I("z"),D(6));
        var radius=All(Imp(Le(D(0),I("z")),Equal(Radius(D(1),D(1),I("z")),Call("ENNRealOfReal",power))),B("z",Real));
        var root=All(Imp(Le(D(0),I("z")),Iff(Equal(Radius(D(1),D(1),I("z")),D(1)),Equal(I("z"),D(1)))),B("z",Real));
        var rate=Equal(Call("weightedFactorRate",language),D(0));
        return Disp(All(Imp(Lt(I("oneStepCeiling"),I("d")),And(Equal(language,Call("singleton",allU)),radius,root,rate)),B("side",I("MemorySide")),B("d",Real)));
    }
    private static DocumentBlock Node(string name, Formula statement, string prose) => Describe.Lean(
        DescribeId.Create(name.Replace('_','-')),DeclarationHandle.Create(Prefix+name),H(name.Replace('_',' ')),
        StatementSource.FromAuthor(statement),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total series of actual retained weighted paths converges exactly below complex spectral radius one, and the full positive-cap scope includes a closed root at one.",
        H("Original weighted spectral convergence boundary"),Blocks(
        Paragraph(Text("The matrix uses exactly the original retained finite-past vertices and allowed c/u labels. Its two edge weights are z to twenty and z to six, summed even when labels have the same endpoints. ComplexAdjacency is the coefficientwise complex image of this real matrix, so every power is the complex image of the original power. WeightedRadius is its complex spectral radius. No replacement graph or assumed exponential-growth law is introduced.")),
        Node("original_weighted_series_boundary",Boundary(),"For every nonnegative real z, both memory sides, every n and K, and every real threshold d, summing all original path monomials over their letter length is convergent exactly when the radius is strictly below one. The exact matrix-power row-sum identity identifies these monomials with the original paths. Nonnegative entries give a sandwich: the operator norm of a power is at most its total entry sum, and that sum is at most the number of retained vertices times the norm. A radius gap gives a summable geometric bound. Conversely convergence forces the powers to tend to zero; a sufficiently late power has norm below one, which forces the spectral radius below one. The empty carrier is handled separately. Thus radius one also gives divergence, and reducible graphs and paths crossing transient bridges remain included."),
        Paragraph(Text("For the endpoint statement, oneStepCeiling is the maximum of zero, the original high-side u intercept, chi times the high-side fixed point, and that fixed point. These are exactly the two one-letter images of the zero and high seeds. A threshold strictly above this ceiling disables every c edge at K=n=1 under both the strict lower and the closed upper conventions.")),
        Node("original_closed_root_boundary",ClosedRoot(),"At these thresholds the complete bilateral language is the singleton all-u sequence. Reconstruction forces every retained vertex to be the one-letter u memory, while the actual all-u path supplies a vertex. The adjacency is therefore the scalar z to six times the identity on this nonempty singleton carrier. Its radius is z to six for nonnegative z, and radius one occurs precisely at z=1. At each actual total weight, at most one different factor occurs: every factor is a u repetition and weight six times its length determines that repetition. Thus the original weightedFactorRate, including its max-one convention at unsupported weights, is zero, equal to minus log base two of the closed root. This positive-K endpoint supplements the original section's K at least two regime."),
        Paragraph(Text("Existence and uniqueness of a spectral root for general thresholds, equality with the original weighted factor rate, memory nesting, auxiliary intersections and inclusions, fixed-graph margins, convergence of graph rates, and eventual even-length asymptotics require further conclusions. The convergence criterion alone does not establish them.")))));
}
