using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class CumulativeRvmErrorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZeroData/CumulativeRvmError";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dyadic logarithmic error controls cumulative counts and shorter ordinate windows.",
        H("Cumulative and short-window zeta zero counts"),
        Blocks(
            Paragraph(Text("Let N(x,y) be the count of nontrivial zeta zeros in the half-open ordinate interval (x,y], with analytic multiplicity. Put c=1/(2 pi) and M(y)=c y (log(y/(2 pi))-1).")),
            Describe.Lean(DescribeId.Create("cumulative-rvm-error"), DeclarationHandle.Create(Owner + ".cumulative_rvm_error"),
                H("Logarithmic-square cumulative counting residual"), StatementSource.FromAuthor(CumulativeBound()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist U>1 and D>=0 such that the displayed inequality holds for every Y>=U. The existing unconditional dyadic Riemann-von Mangoldt estimate has main term exactly M(2x)-M(x). Thus E(x)=N(0,x)-M(x) has increment |E(2x)-E(x)|<=B log(x) for x sufficiently large. The base band [U,2U] has bounded residual by count monotonicity and elementary logarithm bounds. Enlarge D to dominate that base band and to satisfy 2D log(2)>=B. Since D(log(2x)^2-log(x)^2)>=B log(x), induction along dyadic multiples of the base band gives the result for arbitrary real Y>=U."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("short-window-count-lower"), DeclarationHandle.Create(Owner + ".short_window_count_lower"),
                H("Lower counts in windows of logarithmic width"), StatementSource.FromAuthor(WindowBound()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist L>1 and K>0 such that for all real x,y with L<=x, x+K log(x)<=y and y<=2x, the displayed bound holds. For large enough x, monotonicity of the logarithm gives M(y)-M(x)>=c (y-x) log(x)/2. Since y<=2x, the two cumulative errors cost at most 5D log(x)^2. Choosing K>=20D/c makes that cost at most c (y-x) log(x)/4. Count additivity yields the result.")),
                    Paragraph(Text("The classical cumulative Riemann-von Mangoldt formula has a stronger O(log Y) residual. Here the O(log Y)^2 bound follows directly from the existing exact dyadic supplier, without assuming the stronger cumulative estimate or RH. The short-window result gives a lower mass input for phase deficit estimates on moving ordinate bands. Uniform high-order Fourier moments require additional phase estimates."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Sq(Formula a) => F.Seq(a,F.Caret,F.Grp(F.D(2)));
    private static Formula Div(Formula a, Formula b) => F.Seq(F.Frac,F.Grp(a),F.Grp(b));
    private static Formula CumulativeBound() => F.Disp(new Formula.Relation(
        F.Seq(F.Bar,Call("N",F.D(0),I("Y")),F.Minus,Call("M",I("Y")),F.Bar),
        FormulaRelationOperator.LessThanOrEqual,Multiply(I("D"),Sq(Call("log",I("Y"))))));
    private static Formula WindowBound() => F.Disp(new Formula.Relation(
        Div(Multiply(F.Grp(F.Seq(I("y"),F.Minus,I("x"))),Call("log",I("x"))),Multiply(F.D(8),F.Pi)),
        FormulaRelationOperator.LessThanOrEqual,Call("N",I("x"),I("y"))));
}
