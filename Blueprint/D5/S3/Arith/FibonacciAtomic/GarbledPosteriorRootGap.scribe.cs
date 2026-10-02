using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GarbledPosteriorRootGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "A garbled three-class posterior has a positive proper-risk gap for every scalar "
                + "root and every affine softmax head, with unrestricted real parameters.",
            H("Garbled Posterior and Scalar Root Risk"),
            Blocks(Describe.Lean(
                DescribeId.Create("garbled-posterior-root-gap"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A uniform positive gap for both proper losses"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The alphabet W is the existing set of five whole windows 000, 100, "
                            + "010, 101 and 001, written from low to high. Input(m) consists of "
                            + "m+3 independent windows, with each word having mass 5^(-(m+3)). "
                            + "The class is 1 when the high bit of window 0 and the low bit of "
                            + "window 1 are both set. When that event is absent, the class is 2 "
                            + "if the high bit of window 1 and the low bit of window 2 are set; "
                            + "otherwise the class is 0. Windows after index 2 are all retained.")),
                    Paragraph(Text(
                        "Put s=sqrt(2) and mu=(11-6s)/12. The three posterior rows, in label "
                            + "order 0,1,2, are (5/12,s/2-1/3,mu), (7/24,5/12,7/24), "
                            + "and (mu,s/2-1/3,5/12). The joint mass of (x,j) is the uniform "
                            + "word mass times the j-th coordinate of the row selected by its "
                            + "class. The predictor p is the softmax of u_i z(x)+v_i.")),
                    Paragraph(Text(
                        "R_2 is the joint-law expectation of the complete three-label Brier "
                            + "loss sum_i (p_i(x)-1[j=i])^2. Its Bayes value b is the word "
                            + "expectation of 1-sum_i rho_i(x)^2. R_log is the joint-law "
                            + "expectation of -log p_j(x), using natural logarithms. Its Bayes "
                            + "value h is the word expectation of -sum_i rho_i(x) log rho_i(x). "
                            + "These are separate risks and their own Bayes values.")),
                    Paragraph(Text(
                        "No structure is imposed on z. A zero-dimensional root is included "
                            + "by its constant zero scalar embedding. Thus the bound covers "
                            + "every tree, every peak, every internal parameter choice and "
                            + "every tail input. Slopes and biases have no common norm bound.")),
                    Paragraph(Text(
                        "The three target log-odds form a triangle whose distance from any "
                            + "affine line is bounded below at one entire teacher class. "
                            + "An interior logarithm estimate and a separate large-error case "
                            + "turn this separation into a squared probability error. That "
                            + "class has uniform mass at least 16/125. The finite Pinsker "
                            + "inequality transfers the same bound to logarithmic excess risk. "
                            + "The general softmax rank obstruction is discussed by Yang et al. "
                            + "in arXiv:1711.03953 and by Ganea et al. in ICML 2019; the "
                            + "displayed constant belongs to this specified posterior."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Sub(string name, Formula index) => Seq(V(name), Underscore, Grp(index));
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula N(int value) => D(value.ToString(System.Globalization.CultureInfo.InvariantCulture)
        .Select(character => (byte)(character - '0')).ToArray());
    private static Formula Sq(Formula value) => Seq(Par(value), Caret, Grp(D(2)));
    private static Formula LogRatio() => Call("log", Fraction(N(125), N(98)));
    private static Formula Kappa() => F.Kappa;
    private static Formula ResultFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("m"), Sp, InMacro, Sp, Seq(Mathbb, Grp(V("N"))), Comma,
            Sp, Forall, Sp, V("z"), Colon, Call("Input", V("m")), To,
            Seq(Mathbb, Grp(V("R"))), Comma),
        Seq(Forall, Sp, V("u"), Comma, V("v"), Colon, Call("Fin", D(3)), To,
            Seq(Mathbb, Grp(V("R"))), Comma, Sp,
            V("p"), Sp, Colon, Eq, Sp, Call("softmax", V("z"), V("u"), V("v")), Colon),
        Seq(Kappa(), Sp, Le, Sp, Seq(Sub("R", D(2)), Par(V("p"))), Minus, V("b"), Sp, Land,
            Sp, Kappa(), Sp, Le, Sp, Seq(Sub("R", V("log")), Par(V("p"))), Minus, V("h"), Sp, Land),
        Seq(Kappa(), Sp, Eq, Sp, Fraction(Seq(Sq(Mu), Sq(LogRatio())), N(1875)),
            Sp, Eq, Sp,
            Fraction(Seq(N(193), Minus, N(132), Seq(Sqrt, Grp(D(2)))), N(270000)), Sq(LogRatio()),
            Sp, Land, Sp, D(0), Sp, Lt, Sp, Kappa(), Dot),
    ]));
}
