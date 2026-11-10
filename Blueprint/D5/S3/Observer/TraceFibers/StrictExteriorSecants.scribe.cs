using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.TraceFibers;

internal sealed class StrictExteriorSecantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform quantitative inverse on a full positive calibrated matrix fiber.",
        H("Strict Exterior Secant Estimate"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-exterior-uniform-secant"),
            DeclarationHandle.Create("D5/S3/Observer/TraceFibers/StrictExteriorSecants.strict_exterior_uniform_secant"),
            H("One constant for every pair in the fiber"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("All matrix indices are zero based. A legal source is a real two by two matrix with every entry strictly positive, rank one, and trace one. The atomic matrix M has rows (0,1),(1,1). Fix a positive rational theta, viewed as a real number, and a positive real b strictly outside the closed interval with endpoints 1/theta and 1+theta. Both sources range over the entire legal domain with trace(MP)=trace(MQ)=b. The loss is the maximum of the absolute values of all four entries of P-Q.")),
                Paragraph(Text("The constant precedes both source quantifiers. There is no restriction to a compact part of the positive fiber, no exclusion of b=1, and no positive lower bound on source entries. Equal pairs and pairs on different components are included. The scalar compared on the same pair is ell(P)=P10-theta*P11.")),
                Paragraph(Text("Every legal source has the exact positive chart (1+x*r)^(-1) times the matrix with rows (1,r),(x,x*r). In particular its second row is x times its first row, with x>0. Use x for P and y for Q. Put h=Q11-P11, k=Q10-P10, and e=k-theta*h. Trace normalization gives P00-Q00=h; the common calibrated trace gives P01-Q01=h+k.")),
                Paragraph(Text("The two row relations imply (y-x)P00=k+y*h and (y-x)P01=h+y*(h+k). The calibrated trace of P also gives (b-x)P00+((b-1)x-1)P01=0. Multiplying this last equation by y-x and substituting both row relations yields h*A+e*K=0, where B=b-1-theta, C=b*theta-1, A=(B+C)x*y+B(x+y)+C, and K=(b-1)x*y-(x+y)+b. This identity requires no division by a source difference or by y-x.")),
                Paragraph(Text("The exterior condition makes B and C both strictly negative or both strictly positive. Consequently m=min(abs(B),abs(C)) is positive. With W=x*y+x+y+1>0, every coefficient of A has the same sign, and abs(A)>=m*W. Also D=b+abs(b-1)+1>0 satisfies abs(K)<=D*W by the triangle inequality. Taking absolute values in the identity and canceling W gives abs(h)<=R*abs(e), where R=D/m is finite and nonnegative.")),
                Paragraph(Text("Since k=e+theta*h, the triangle inequality gives abs(k)<=(1+theta*R)abs(e) and abs(h+k)<=(1+(1+theta)R)abs(e). Thus L=1+(1+theta)R controls the two diagonal differences, the lower left difference k, and the upper right difference h+k simultaneously. The absolute value of e is exactly the scalar separation in the statement. This proves the estimate uniformly even as entries approach zero.")),
                Paragraph(Text("For canonical chronological continuation, GainRay.acquisition_append and acquisition_pure identify the word of S copies of M followed by J with J*M^S. The original GraftAffineClosure.result Fibonacci packet gives trace(J*M^S*P)=F_S+F_(S-1)*b+F_S*ell(P), with theta=F_(S-1)/F_S and S>=2. Since F_S>0, the estimate gives maxEntry(P-Q)<=(L/F_S)*abs(trace(J*M^S*P)-trace(J*M^S*Q)). Thus Theorem 22.1's chronological continuation with S=T+n-1 receives a global Lipschitz pair estimate at exactly its strict exterior parameters.")),
                Paragraph(Text("For Theorem 23.1's first positive nonroot offset r, execute M at each earlier offset and J at r; then S=T+r-1. The known gain at that original clock is nonzero. Removing the same known drift and dividing by that gain converts raw error delta to effective trace error delta/abs(H(T+r)). Two legal candidates consistent with one received scalar therefore have distance at most 2*L*delta/(F_S*abs(H(T+r))). Every earlier root action and read remains paid. This pair estimate supplies the quantitative input; this module does not formalize the compact-closure projection decoder, its minimax guarantees, endpoint behavior, all word necessity, or the full stable-cost classification."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula theta = Theta, b = F.Id("b"), l = F.Id("L"), p = F.Id("P"), q = F.Id("Q");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula mat = App("Mat", D(2), real);
        Formula inverse = new Formula.Fraction(D(1), theta);
        Formula upper = Seq(D(1), Plus, theta);
        Formula exterior = Seq(Open, b, Sp, Lt, Sp, App("min", inverse, upper), Sp,
            Lor, Sp, App("max", inverse, upper), Sp, Lt, Sp, b, Close);
        Formula legal = Seq(App("LegalSource", p), Sp, Land, Sp, App("LegalSource", q), Sp,
            Land, Sp, App("tr", Seq(F.Id("M"), p)), Sp, Eq, Sp, b, Sp, Land, Sp,
            App("tr", Seq(F.Id("M"), q)), Sp, Eq, Sp, b);
        Formula scalarP = Seq(Entry(p, 1, 0), Minus, theta, Cdot, Sp, Entry(p, 1, 1));
        Formula scalarQ = Seq(Entry(q, 1, 0), Minus, theta, Cdot, Sp, Entry(q, 1, 1));
        Formula estimate = Seq(App("maxEntry", Seq(p, Minus, q)), Sp, Le, Sp, l, Cdot, Sp,
            App("abs", Seq(Open, scalarP, Close, Minus, Open, scalarQ, Close)));
        Formula pair = Seq(Forall, Sp, p, Comma, Sp, q, Colon, Sp, mat, Comma, Sp,
            Open, legal, Close, Sp, Rightarrow, Sp, estimate);
        return Disp(Seq(Forall, Sp, theta, Colon, Sp, rational, Comma, Sp,
            Forall, Sp, b, Colon, Sp, real, Comma, Sp,
            Open, theta, Sp, Gt, Sp, D(0), Sp, Land, Sp, b, Sp, Gt, Sp, D(0), Sp,
            Land, Sp, exterior, Close, Sp, Rightarrow, Sp,
            Exists, Sp, l, Colon, Sp, real, Comma, Sp, l, Sp, Ge, Sp, D(0), Sp,
            Land, Sp, Grp(pair)));
    }

    private static Formula Entry(Formula matrix, byte row, byte column)
        => new Formula.Subscript(matrix, Seq(D(row), Comma, D(column)));

    private static Formula App(string name, params Formula[] arguments)
        => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
