using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class FractionalBranchGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fractional logarithmic mixture lies strictly below its mean vector. When the mean variance is below the distance floor, the actual lower-corner budget determines nested positive support points.",
        H("Fractional means and residual support geometry"),
        Blocks(
            Paragraph(Text(
                "Write f(x)=log(1-exp(-x)) for real x>0. The two-point distance v=gridDistance(a,m,c,d) is the minimum of the distances from c and d to the closed interval [a,m]. All scalar parameters below are real.")),
            Describe.Lean(
                DescribeId.Create("positive-logarithmic-strict-concavity"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/FractionalBranchGeometry.logValue_strictConcaveOn"),
                H("Strict concavity on positive arguments"),
                StatementSource.FromAuthor(Disp(Seq(Mixture, Lt, Fn(Z)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function f is strictly concave on (0,infinity). Equivalently, for every pair of distinct positive real numbers c,d and every 0<theta<1, let z=(1-theta)c+theta*d; the displayed inequality holds. The second derivative is -exp(x)/(exp(x)-1)^2<0 throughout the positive half-line, and f is continuous there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fractional-mean-variance-envelope"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_mean_branch"),
                H("The branch whose mean variance meets the floor"),
                StatementSource.FromAuthor(Disp(Seq(Mixture, Plus, SumOther(Fn(T)), Lt,
                    SumAll(Fn(Y)), Sp, Le, Sp, Psi(V), Sp, Le, Sp, Psi(Vzero)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k>=2 be a natural number, let j belong to Fin k, and let t:Fin k->R. Assume 0<c<d, 0<theta<1, and t(i)>0 for i distinct from j. Put z=(1-theta)c+theta*d, y(j)=z and y(i)=t(i) otherwise. Assume the saturated budget z+sum_{i!=j}t(i)=km. Set s=z-m, W=sum_{i!=j}(t(i)-m)^2, and V=s^2+W. For every V0 with 0<=V0<=V, the three displayed comparisons hold.")),
                    Paragraph(Text(
                        "The positive vector y has mean m>0, total squared deviation V, and V<k(k-1)m^2. Its genuinely fractional row gives the first, strict comparison. The positive-coordinate envelope gives the second comparison, and variance antitonicity gives the third. The cases V=V0, V0=0, and V=V0=0 are included. No nonzero variance or distinct Hermite nodes are assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residual-distance-straddling"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/FractionalBranchGeometry.residual_distance_geometry"),
                H("A residual gap forces both endpoints outside the interval"),
                StatementSource.FromAuthor(Disp(Seq(AbsS, Lt, LowerV, Sp, Land, Sp,
                    C, Lt, A, Sp, Land, Sp, M, Lt, Dpoint, Sp, Land, Sp,
                    LowerV, Eq, MinDistance, Sp, Land, Sp, D(0), Lt, LowerV))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume a<m and c<z<d. Let W and V0 be arbitrary real numbers, put s=z-m and v=gridDistance(a,m,c,d), and assume s^2+W<V0<=v^2+W. No sign assumption on W or the endpoints is needed for this statement.")),
                    Paragraph(Text(
                        "Nonnegativity of distance and the strict squared inequality give |s|<v. An endpoint in [a,m] would make v zero. If c>=m, its distance to m is smaller than z-m; if d<=a, its distance to a is smaller than m-z. Both possibilities contradict |s|<v. Thus c<a<m<d. The nearest interval points to c and d are respectively a and m, giving v=min(a-c,d-m)>0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fractional-positive-nested-support"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_residual_support"),
                H("The lower-corner budget gives nested positive support"),
                StatementSource.FromAuthor(Disp(Seq(AbsS, Lt, LowerV, Sp, Land, Sp,
                    C, Lt, A, Sp, Land, Sp, M, Lt, Dpoint, Sp, Land, Sp,
                    LowerV, Eq, MinDistance, Sp, Land, Sp,
                    K, LowerV, Sp, Le, Sp, Open, K, Minus, D(1), Close,
                    Open, M, Minus, C, Close, Minus, S, Sp, Land, Sp,
                    D(0), Lt, C, Sp, Le, Sp, InnerC, Lt, M, Minus, LowerV, Lt, Z,
                    Lt, M, Plus, LowerV, Eq, InnerD, Sp, Le, Sp, Dpoint))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k>=2 be a natural number, j in Fin k, and t:Fin k->R. Assume 0<c<d, 0<theta<1, and a<m. Put z=(1-theta)c+theta*d, s=z-m, W=sum_{i!=j}(t(i)-m)^2, and v=gridDistance(a,m,c,d). Assume z+sum_{i!=j}t(i)=km, ka<=c+sum_{i!=j}t(i), and s^2+W<V0<=v^2+W. Positivity of the other coordinates is not required by this geometric implication.")),
                    Paragraph(Text(
                        "Define n=k-1, A=(kv+s)/n, C=m-A, and D=m+v. Here C and D denote the inner endpoints c' and d'. The residual distance result gives c<a<m<d, v=min(a-c,d-m)>0, and -v<s<v. The actual lower-corner budget then gives kv<=k(a-c)<=(k-1)(m-c)-s. Consequently A<=m-c and v<A, proving the full displayed support chain. These are analytic support points; no membership in the original two-point grids or feasibility as an actual corner is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-fractional-branch-alternative"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_branch_alternative"),
                H("The exhaustive two-branch alternative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Vzero, Sp, Le, Sp, V, Sp, Land, Sp, Mixture, Plus, SumOther(Fn(T)),
                    Lt, SumAll(Fn(Y)), Sp, Le, Sp, Psi(V), Sp, Le, Sp, Psi(Vzero), Close,
                    Sp, Lor, Sp, Open, V, Lt, Vzero, Sp, Land, Sp,
                    AbsS, Lt, LowerV, Sp, Land, Sp, C, Lt, A, Sp, Land, Sp,
                    M, Lt, Dpoint, Sp, Land, Sp, LowerV, Eq, MinDistance, Sp, Land, Sp,
                    K, LowerV, Sp, Le, Sp, Open, K, Minus, D(1), Close,
                    Open, M, Minus, C, Close, Minus, S, Sp, Land, Sp,
                    D(0), Lt, C, Sp, Le, Sp, InnerC, Lt, M, Minus, LowerV, Lt, Z,
                    Lt, M, Plus, LowerV, Eq, InnerD, Sp, Le, Sp, Dpoint, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k>=2, j in Fin k, t:Fin k->R, 0<c<d, 0<theta<1, and a<m. Require t(i)>0 for i distinct from j. Use z=(1-theta)c+theta*d, y(j)=z and y(i)=t(i) otherwise, s=z-m, W=sum_{i!=j}(t(i)-m)^2, V=s^2+W, v=gridDistance(a,m,c,d), C=m-(kv+s)/(k-1), and D=m+v. Assume z+sum_{i!=j}t(i)=km, ka<=c+sum_{i!=j}t(i), and 0<=V0<=v^2+W.")),
                    Paragraph(Text(
                        "Comparison of V0 and V gives exactly one of the displayed branches. When V0<=V, strict concavity and the moment envelope give all three objective comparisons. When V<V0, the distance and lower-corner budget give all the nested support inequalities. Equality of the two variances belongs to the first branch."))),
                DescribeRole.Theorem))));

    private static Formula C => F.Id("c");
    private static Formula Dpoint => F.Id("d");
    private static Formula A => F.Id("a");
    private static Formula M => F.Id("m");
    private static Formula K => F.Id("k");
    private static Formula S => F.Id("s");
    private static Formula V => F.Id("V");
    private static Formula Vzero => Seq(V, Underscore, Grp(D(0)));
    private static Formula LowerV => F.Id("v");
    private static Formula Z => F.Id("z");
    private static Formula InnerC => F.Id("C");
    private static Formula InnerD => F.Id("D");
    private static Formula T => Call("t", F.Id("i"));
    private static Formula Y => Call("y", F.Id("i"));
    private static Formula Fn(Formula x) => Call("f", x);
    private static Formula Psi(Formula v) => Call("psiK", K, M, v);
    private static Formula AbsS => Seq(Bar, S, Bar);
    private static Formula MinDistance => Call("min", Seq(A, Minus, C), Seq(Dpoint, Minus, M));
    private static Formula Mixture => Seq(Open, D(1), Minus, Theta, Close, Fn(C), Plus, Theta, Fn(Dpoint));
    private static Formula SumOther(Formula f) => Seq(Sum, Underscore,
        Grp(F.Id("i"), Neq, F.Id("j")), f);
    private static Formula SumAll(Formula f) => Seq(Sum, Underscore, Grp(F.Id("i")), f);
}
