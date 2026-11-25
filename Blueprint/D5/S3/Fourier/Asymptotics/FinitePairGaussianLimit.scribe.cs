using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class FinitePairGaussianLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/FinitePairGaussianLimit";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered pair fourth moment controls the squared Fourier score and provides a Gaussian central window.",
        H("Central Gaussian profiles from pair moments"),
        Blocks(
            Paragraph(Text("For a finite real frequency family g and real weights w, let W be the total weight, Q(t) the squared norm of the complex score, and M(k) the sum over all ordered pairs of w(i)w(j)(g(i)-g(j))^k. PairNonnegative(w) means all pair products are nonnegative. The formulas allow varying finite families indexed by degree n, using the subscript n for the corresponding quantities.")),
            Describe.Lean(DescribeId.Create("quartic-control"), DeclarationHandle.Create(Owner + ".score_quartic"),
                H("Global fourth-moment control"), StatementSource.FromAuthor(Quartic()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Specialize FiniteTailMomentMissingWindow.score_even_expansion to degree one. Each occupation is supported at exactly one index with value one, so its multinomial weight and frequency are the original weight and frequency. Apply FiniteSincCollisionMoment.phase_re to obtain the pair cosine sum. The scalar cosine remainder is between zero and x^4/24 by AccumulatedSagittaPhases.versine_ge and the quadratic cosine lower bound. Sum the scalar inequalities with the nonnegative pair products."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-limit"), DeclarationHandle.Create(Owner + ".score_gaussian_limit"),
                H("Central Gaussian power limit"), StatementSource.FromAuthor(Limit()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume eventually the pair products are nonnegative, W_n=1, and M_n(2)>0. Write s_n=sqrt(n M_n(2)/2), R_n=M_n(4)/(n M_n(2)^2), and P_n(u)=Q_n(u/s_n)^n. For positive n the finite estimate after rescaling bounds n(Q_n(u/s_n)-1)+u^2 between zero and u^4 R_n/6. If R_n tends to zero, the latter error tends to zero at each fixed u. The standard exponential power limit yields P_n(u) tending to exp(-u^2)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-envelope"), DeclarationHandle.Create(Owner + ".score_gaussian_envelope"),
                H("Gaussian envelope on a fourth-moment window"), StatementSource.FromAuthor(Envelope()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a single normalized finite family and positive n, write s=sqrt(n M(2)/2) and P(u)=Q(u/s)^n. If u^2 M(4)<=3n M(2)^2, the quartic error is at most u^2/2 after multiplication by n. Hence Q(u/s)<=1-u^2/(2n)<=exp(-u^2/(2n)). Raising to the nth power is valid because Q is a squared norm. This provides an integrable Gaussian bound across every admissible central window. Noncentral contributions to whole-line Fejer moments require additional estimates."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Pow(Formula a, byte n) => F.Seq(a,F.Caret,F.Grp(F.D(n)));
    private static Formula Div(Formula a, Formula b) => F.Seq(F.Frac,F.Grp(a),F.Grp(b));
    private static Formula M(byte k) => Call("M",F.D(k));
    private static Formula Quartic()
    {
        Formula t = I("t");
        Formula error = Subtract(Call("Q",t), Subtract(Pow(I("W"),2),Div(Multiply(M(2),Pow(t,2)),F.D(2))));
        return F.Disp(Imp(Call("PairNonnegative",I("w")),And(Le(F.D(0),error),Le(error,Div(Multiply(M(4),Pow(t,4)),F.D(2,4))))));
    }
    private static Formula Tends(Formula x, Formula y) => Call("Tendsto",x,I("atTop"),Call("nhds",y));
    private static Formula Limit()
    {
        Formula u = I("u");
        return F.Disp(Imp(And(Call("Eventually",Call("PairNonnegative",I("w"))),And(Call("Eventually",Equal(I("W"),F.D(1))),And(Call("Eventually",Lt(F.D(0),M(2))),Tends(I("R"),F.D(0))))),Tends(Call("P",u),Call("exp",Subtract(F.D(0),Pow(u,2))))));
    }
    private static Formula Envelope()
    {
        Formula u = I("u"), n = I("n");
        Formula assumption = And(Call("PairNonnegative",I("w")),And(Equal(I("W"),F.D(1)),And(Lt(F.D(0),n),And(Lt(F.D(0),M(2)),Le(Multiply(Pow(u,2),M(4)),Multiply(Multiply(F.D(3),n),Pow(M(2),2)))))));
        return F.Disp(Imp(assumption,Le(Call("P",u),Call("exp",Div(Subtract(F.D(0),Pow(u,2)),F.D(2))))));
    }
}
