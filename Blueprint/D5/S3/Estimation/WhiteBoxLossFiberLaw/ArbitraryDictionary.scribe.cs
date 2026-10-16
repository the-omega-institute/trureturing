using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.WhiteBoxLossFiberLaw;

internal sealed class ArbitraryDictionaryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef RadialSource =
        LibraryNoteRef.Create("D5/L/SparseCoding/parikhboyd2014proximal");
    private static readonly LibraryNoteRef MergingSource =
        LibraryNoteRef.Create("D5/L/SparseCoding/mais2026superposition");
    private static Formula Flow(params Formula[] xs) => Seq(xs.SelectMany(
        (x,j) => j == 0 ? new[]{x} : new[]{Sp,x}).ToArray());
    private static Formula Sub(Formula x, Formula y) => Flow(x, Underscore, Grp(y));
    private static Formula Sq(Formula x) => Flow(x, Caret, Grp(D(2)));
    private static Formula Norm(Formula x) => Flow(Vert,x,Vert);
    private static Formula Call(string name, params Formula[] xs) => Flow(F.Id(name),Open,
        Flow(xs.SelectMany((x,j) => j == 0 ? new[]{x} : new[]{Comma,x}).ToArray()),Close);
    private static readonly Formula lam = LambdaLower, x = F.Id("x"), e = F.Id("e"),
        c = F.Id("c"), d = F.Id("d"), i = F.Id("i"), j = F.Id("j"),
        u = F.Id("u"), v = F.Id("v"), w = F.Id("w"), b = F.Id("b"),
        B = F.Id("B"), n = F.Id("n"), dic = F.Id("D");
    private static Formula Cost(Formula signal) => Call("C",signal,dic);
    private static Formula Energy(Formula signal, Formula code) => Call("E",signal,dic,code);
    private static Formula Floor() => Flow(lam,n,Minus,Frac,Grp(Sq(lam)),Grp(D(2)));
    private static Formula Mass(Formula amount) => Flow(Sum,Underscore,Grp(i),Sub(c,i),Eq,amount);
    private static Formula Support(Formula direction) => Flow(Forall,i,Comma,Sub(c,i),Neq,D(0),
        Rightarrow,Sub(d,i),Eq,direction);
    private static Formula Contains(Formula direction) => Flow(Exists,i,Comma,Sub(d,i),Eq,direction);
    private static Formula Joint(Formula dictionary) => Call("J",dictionary);
    private static Formula Pair(Formula a, Formula z) => Flow(OpenBracket,a,Comma,z,CloseBracket);
    private static Formula Gap() => Flow(b,lam,Open,D(2),Minus,Sqrt,Grp(D(2)),Minus,
        Frac,Grp(lam),Grp(D(2)),Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact sparse coding and absorption for every finite normalized dictionary.",
        H("Arbitrary Finite Dictionaries"),
        Blocks(
            Paragraph(Text("Let I be any finite index type, including the empty type. " +
                "In a real inner-product space, D assigns a unit vector d_i to each i in I. " +
                "Entries may repeat, and neither linear independence nor containment in the data plane is required. " +
                "A feasible code has c_i>=0, Dc denotes the sum of c_i d_i, and " +
                "E(x,D,c)=norm(x-Dc)^2/2+lambda sum_i c_i. C(x,D) is its infimum over feasible codes. " +
                "For lambda>0 the infimum is attained: codes improving on zero lie in the compact box " +
                "0<=c_i<=norm(x)^2/(2 lambda), and E is continuous.")),
            Paragraph(Text("The radial lower value is the Euclidean-norm proximal value in Parikh and Boyd, " +
                "Proximal Algorithms, Section 6.5.1. The alignment and splitting statements describe its equality case " +
                "for a finite normalized dictionary. The two-entry positive-penalty merging proposition of the MAIS-A3 " +
                "research draft gives the two-entry precedent for the absorption statement; that draft is not peer reviewed. " +
                "The statements below allow every finite number of entries and the full range 0<lambda<1 in the orthogonal model.")),
            Describe.Lean(
                DescribeId.Create("single-point-radial"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/ArbitraryDictionary.single_point_radial"),
                H("Radial equality and every optimal splitting"),
                StatementSource.FromAuthor(Disp(Flow(
                    Flow(Floor(),Le,Cost(x),Land,Open,Cost(x),Eq,Floor(),Iff,Contains(e),Close), Nl,
                    Flow(Forall,c,Ge,D(0),Comma,Energy(x,c),Eq,Floor(),Iff,
                        Open,Mass(Flow(n,Minus,lam)),Land,Support(e),Close), Nl,
                    Flow(Forall,i,Comma,Sub(d,i),Eq,e,Rightarrow,
                        Open,Sub(c,i),Eq,Flow(n,Minus,lam),Comma,Forall,j,Neq,i,Comma,Sub(c,j),Eq,D(0),Close,
                        Rightarrow,Energy(x,c),Eq,Cost(x))))),
                AssessedProvenance.FromRepo(RadialSource),
                Blocks(Paragraph(Text("Assume 0<lambda<norm(x), and put n=norm(x), e=x/n. " +
                    "The first line gives the radial floor and says that equality holds exactly when D contains e. " +
                    "The second line characterizes every feasible code attaining that floor: its total mass is n-lambda " +
                    "and every nonzero coordinate belongs to an entry equal to e. Thus every nonnegative splitting of " +
                    "n-lambda among repeated copies of e is optimal. In particular, the third line's single-coordinate " +
                    "code is feasible and optimal for every index whose entry equals e. " +
                    "For n>lambda the mass is positive, so the empty dictionary cannot attain the radial floor.")),
                    Paragraph(Text("For x=n e with norm(e)=1, square completion expresses the excess as " +
                    "norm((n-lambda)e-Dc)^2/2+lambda sum_i c_i(1-inner(e,d_i)). " +
                    "Every summand is nonnegative. At equality the residual vanishes, and each active entry has " +
                    "inner(e,d_i)=1, hence d_i=e by the equality case of Cauchy-Schwarz. " +
                    "Taking the inner product with e determines the total mass. Attainment converts this " +
                    "energy characterization into the exact criterion for the infimal cost."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("whitebox-absorption"),
                DeclarationHandle.Create("D5/S3/Estimation/WhiteBoxLossFiberLaw/ArbitraryDictionary.whitebox_absorption"),
                H("Global absorption and the faithful dictionary gap"),
                StatementSource.FromAuthor(Disp(Flow(
                    Flow(B,Le,Joint(dic),Land,Open,Joint(dic),Eq,B,Iff,
                        Open,Contains(u),Land,Contains(w),Close,Close), Nl,
                    Flow(Joint(dic),Eq,B,Rightarrow,Forall,c,Ge,D(0),Comma,
                        Energy(Flow(u,Plus,v),c),Eq,Cost(Flow(u,Plus,v)),Iff,
                        Open,Mass(Flow(Sqrt,Grp(D(2)),Minus,lam)),Land,Support(w),Close), Nl,
                    Flow(Joint(Pair(u,w)),Eq,B,Comma,Joint(Pair(u,v)),Minus,B,Eq,Gap(),Gt,D(0),
                        Comma,B,Lt,Joint(Pair(u,v)))))),
                AssessedProvenance.FromRepo(RadialSource, MergingSource),
                Blocks(Paragraph(Text("Let u,v be orthogonal unit vectors, w=(u+v)/sqrt(2), " +
                    "0<lambda<1 and a,b>0. For any real p0 set J(D)=p0 C(0,D)+a C(u,D)+b C(u+v,D) " +
                    "and B=a(lambda-lambda^2/2)+b(sqrt(2)lambda-lambda^2/2). " +
                    "Probability weights on the support {0,u,u+v} are a special case; the zero-point cost is zero. " +
                    "Every finite normalized dictionary has objective at least B, and the pair [u,w] attains B. " +
                    "Consequently B is the global minimum even when the number of dictionary entries varies. " +
                    "Its minimizers are exactly the dictionaries containing both u and w. " +
                    "At every such minimizer all optimal codes for u+v have total mass sqrt(2)-lambda " +
                    "and are supported only on entries equal to w, including arbitrary nonnegative splittings among repeats. " +
                    "The faithful pair [u,v] has exactly the positive excess displayed above and is strictly suboptimal.")),
                    Paragraph(Text("Positive weights force both sample costs to meet their individual radial floors. " +
                    "The single-point equality criterion then identifies both required directions. " +
                    "For the faithful orthogonal pair, square completion separates the two code coordinates, " +
                    "each minimized at 1-lambda, so C(u+v,[u,v])=2 lambda-lambda^2. " +
                    "Subtracting the radial value yields the displayed gap; sqrt(2)<3/2 and lambda<1 make it positive."))),
                DescribeRole.Theorem))));
}
