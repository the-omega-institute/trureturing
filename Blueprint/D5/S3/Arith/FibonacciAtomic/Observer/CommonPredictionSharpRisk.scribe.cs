using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class CommonPredictionSharpRiskDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, F.Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp threshold for simultaneous deterministic prediction of a two-layer teacher family.", H("Sharp Common Prediction Risk"), Blocks(
            Paragraph(Text("Each of n complete windows is independent with masses (1-3s)/2, s, (1-3s)/2, s, s in alphabet order zero, low, middle, ends, high. Risk is the expectation of a zero-one classification mistake for the original priority teacher.")),
            Paragraph(Text("Coordinates in Fin(n) start at zero. Fix q<r<v with q positive and put m=q.val. The family has 2m teachers: (i,q,r) and (i,r,v) for every i<q. In positions numbered from one, these are precisely the teachers (p,q,r) and (p,r,v) with 1<=p<q, and m=q-1.")),
            Paragraph(Text("Let K have binomial law with m trials and success probability 2s. Define G(m,k)=2 min(k,m-k)+min(2k,m-k). The threshold T(m,s) is 8s^2-18s^3+4s^4 plus (s^2/m) times the binomial expectation of G(m,K). The sums include both endpoints k=0 and k=m.")),
            Paragraph(Text("For 0<s<=1/5, one deterministic classifier gives exactly T(m,s) to every teacher. Every deterministic classifier has some teacher whose risk is at least T(m,s). Equivalently, all teacher risks can be at most epsilon simultaneously exactly when T(m,s)<=epsilon.")),
            Paragraph(Text("The balanced selector attains the pointwise average-risk lower bound. Integrating the three anchors gives an expression in the prefix endpoint count. Its binomial mean produces the explicit threshold. Coordinates outside the selected prefix and three anchors integrate to total mass one, so arbitrary gaps and additional coordinates do not change the threshold.")),
            Paragraph(Text("The result concerns this two-layer subfamily on the independent complete-window law. It does not identify the minimax risk of the family of all increasing triples or of a seam-conditioned input law.")),
            Describe.Lean(DescribeId.Create("sharp-common-risk"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk.sharp_risk_full"),
                H("Attainment, lower bound and tolerance equivalence"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Classwise balance gives equal risks under every nonnegative rare-class weight. Pointwise majority attains the average lower bound. The anchor and binomial formulas identify this value with T. A coordinate embedding transports the common classifier to arbitrary ordered anchors, and marginalization removes unused coordinates. Finally the finite teacher family has a risk maximizer, which yields the stated worst-teacher lower bound."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var family = Call("TeacherFamily", V("q"));
        var input = Call("Input", V("n"));
        var risk = Call("gappedRisk", V("q"), V("r"), V("v"), V("qr"), V("rv"),
            V("s"), V("f"), V("t"));
        var threshold = Call("T", Call("val", V("q")), V("s"));
        var attains = Ex("f", Call("Function", input, Call("Fin", D(3))),
            All("t", family, Eq(risk, threshold)));
        var lower = All("f", Call("Function", input, Call("Fin", D(3))),
            Ex("t", family, Le(threshold, risk)));
        var feasible = Ex("f", Call("Function", input, Call("Fin", D(3))),
            All("t", family, Le(risk, V("epsilon"))));
        var tolerance = All("epsilon", V("Real"),
            Seq(Par(feasible), Sp, Iff, Sp, Par(Le(threshold, V("epsilon")))));
        return All("n", V("Nat"), All("q", Call("Fin", V("n")),
            All("r", Call("Fin", V("n")), All("v", Call("Fin", V("n")),
                Imp(Seq(D(0), Sp, Lt, Sp, Call("val", V("q"))),
                    All("qr", Seq(V("q"), Sp, Lt, Sp, V("r")),
                        All("rv", Seq(V("r"), Sp, Lt, Sp, V("v")),
                            All("s", V("Real"),
                                Imp(And(Seq(D(0), Sp, Lt, Sp, V("s")),
                                    Le(V("s"), new Formula.Fraction(D(1), D(5)))),
                                    And(attains, And(lower, tolerance)))))))))));
    }
}
