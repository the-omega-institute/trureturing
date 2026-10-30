using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ProductAbsorptionLogMomentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/localproductabsorption");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact first logarithmic moment of the product absorption kernel is nonnegative on the closed unit square.",
        H("Nonnegative Logarithmic First Moment"), Blocks(
            Describe.Lean(DescribeId.Create("product-log-moment-nonneg"),
                DeclarationHandle.Create("D5/S3/Entropy/ProductAbsorptionLogMoment.product_log_moment_nonneg"),
                H("The closed-square moment inequality"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For every real u,v in [0,1], let A=u+v, B=uv, L=A-B, "
                        + "q=sqrt(B(1-A+B)) and Mplus=A-2B+2q, Mminus=A-2B-2q. The conclusion is "
                        + "2Llog(L)-ulog(u)-vlog(v)-(Mplus*log(Mplus)+Mminus*log(Mminus))/2>=0. "
                        + "This is the actual productLogMoment definition, with natural logarithms and 0log0=0. "
                        + "The formula includes all parameter edges, u=v and every zero root.")),
                    Paragraph(Text("For 0<u<=v<1 set p=u/A, t=B/A, d=1-2p and s=1-2t. Then "
                        + "0<p<=1/2, 0<=t<=p, and the roots divided by A are s plus or minus sqrt(s^2-d^2). "
                        + "The moment equals A*D_p(t), where "
                        + "D_p(t)=binEntropy(p)+2(1-t)log(1-t)-g_d(1-2t) and "
                        + "g_d(s)=((s+q)log(s+q)+(s-q)log(s-q))/2 for q=sqrt(s^2-d^2). "
                        + "Every coefficient of log(A) cancels in this exact scaling identity.")),
                    Paragraph(Text("For d>0 and s>d, with r=sqrt(s^2-d^2)/s, differentiation gives "
                        + "g_d''(s)=(r-(1-r^2)artanh(r))/(s*r^3). The derivative of "
                        + "(r-(2/3)r^3)/(1-r^2)-artanh(r) is (2/3)r^4/(1-r^2)^2>=0. "
                        + "Its value at zero is zero, so g_d''(s)>=2/(3s). For d=0 use "
                        + "g_0(s)=slog(2s), which has curvature 1/s. Consequently "
                        + "D_p''(t)=2/(1-t)-4g_d''(1-2t)<=0 throughout 0<t<p. "
                        + "Continuity extends concavity to [0,p], with no endpoint derivative assumption.")),
                    Paragraph(Text("At t=0, D_p(0)=binEntropy(p)+binEntropy((1+sqrt(1-d^2))/2)-log(2). "
                        + "The exact entropy integral gives F(x)>=xlog(2) for F(x)=binEntropy((1+sqrt(1-x))/2). "
                        + "Apply this at x=d^2 and x=1-d^2 to get D_p(0)>=0. At t=p the roots coincide "
                        + "and D_p(p)=(1-p)binEntropy(p/(1-p))>=0, including p=1/2. "
                        + "The minimum principle for concave functions proves the interior moment inequality. "
                        + "Symmetry and the exact edge formulas moment(0,v)=0 and moment(1,v)=binEntropy(v) "
                        + "prove the whole closed square.")),
                    Paragraph(Text("The local unpublished scalar proof supplies the mathematical argument. "
                        + "This theorem supplies the missing sign of the unweighted kernel integral. "
                        + "The decreasing-weight argument and actual binary-entropy scalar inequality consume it; "
                        + "it alone is not a density-state or quantum-channel absorption theorem."))), DescribeRole.Theorem))));

    private static Formula N(string n) => F.Id(n);
    private static Formula R() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula x) => Seq(Forall, Sp, Par(Seq(N(n), Colon, Sp, R())), Comma, Sp, x);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, y);
    private static Formula Inside(Formula x) => And(Le(D(0), x), Le(x, D(1)));
    private static Formula Statement() => All("u", All("v", Imp(Inside(N("u")), Imp(Inside(N("v")),
        Le(D(0), Call("productLogMoment", N("u"), N("v")))))));
}
