using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class LorentzLocalCoefficientKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/LorentzLocalCoefficientKernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse central-moment corrections give endpoint-sensitive local coefficient bounds.",
        H("The Local Lorentz Coefficient Kernel"),
        Blocks(
            Paragraph(Text("The central moment is the Bernstein average of (i-mX) raised to its "
                + "order. Its inverse convolution defines tau(m,n), with tau(m,0)=1. Write "
                + "C(D,J,P) for the normalized Bernstein coefficient transform and R(m,p) for "
                + "max(sqrt(p(1-p)/m),1/m). The polynomial Q(m,r,f) uses the prescribed jet f(n,i), "
                + "the correction tau(m,n)/m^n, and the degree-m Bernstein basis, summed over "
                + "n from zero to r and i from zero to m.")),
            Entry("correction-coefficients", "tau_coefficient_bound", "Both ends of the correction array",
                CorrectionFormula(), true,
                "For each correction order n, one constant controls every positive grid size m "
                + "and every coefficient h from zero through n. Reflection supplies the symmetric "
                + "minimum of the two endpoint bounds. This is Corollary 16 of Holtz, Nazarov "
                + "and Peres in the normalized Bernstein basis; the proof here obtains the "
                + "coefficient estimate from complex disk bounds for the actual moments."),
            Entry("weighted-correction", "weighted_tau_bound", "Hypergeometric averaging of the correction",
                WeightedFormula(), false,
                "The weight w(D,J,n,h) is choose(n,h) times the falling factorials (J)h and "
                + "(D-J)(n-h), divided by (D)n. When 2n is at most D, weighting the actual "
                + "correction array gives the nth power of the endpoint-adapted radius, "
                + "with a constant depending only on n."),
            Entry("local-jets", "local_coefficient_bound", "Only the effective local jets are needed",
                LocalFormula(), false,
                "One constant depending only on r controls all output coefficients, including "
                + "J=0 and J=m+r. For each derivative order, only grid entries with i at most J "
                + "and J at most i+r contribute. Arbitrary complex jets satisfying the displayed "
                + "local bounds are allowed. This coefficient estimate refines the function-based "
                + "estimates around Lemma 24 of Holtz, Nazarov and Peres. It requires r at most m; "
                + "the polynomial remainder theorem uses reproduction outside its nonzero regime."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, bool literature, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(I(name), [.. args]);
    private static Formula Field(string name) => Seq(Mathbb, Grp(I(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Correction(Formula n, Formula h, Formula m) =>
        Call("C", n, h, Fr(Call("tau", m, n), Pow(m, n)));
    private static Formula Constant(string order, Formula body) => All(order, Field("N"),
        Ex("K", Field("R"), Seq(D(1), Le, Sp, I("K"), Land, Sp, body)));

    private static Formula CorrectionFormula()
    {
        Formula n = I("n"), m = I("m"), h = I("h"), k = I("K");
        return Disp(Constant("n", All("m", Field("N"), Seq(D(0), Lt, Sp, m, Rightarrow, Sp,
            All("h", Field("N"), Seq(h, Le, Sp, n, Rightarrow, Sp,
                Norm(Correction(n,h,m)), Le, Sp, k, Cdot, Sp,
                Call("min", Fr(Pow(m,h),Pow(m,n)), Fr(Pow(m,Seq(n,Minus,h)),Pow(m,n)))))))));
    }

    private static Formula WeightedFormula()
    {
        Formula n = I("n"), m = I("m"), degree = I("D"), j = I("J"), h = I("h");
        Formula sum = Seq(Sum, Underscore, Grp(h, Eq, D(0)), Caret, Grp(n), Sp,
            Call("w", degree,j,n,h), Cdot, Sp, Norm(Correction(n,h,m)));
        Formula body = Seq(D(0), Lt, Sp, m, Land, Sp, D(0), Lt, Sp, degree, Land, Sp,
            D(2), Cdot, Sp, n, Le, Sp, degree, Land, Sp, j, Le, Sp, degree, Rightarrow, Sp,
            sum, Le, Sp, I("K"), Cdot, Sp, Pow(Call("R",m,Fr(j,degree)),n));
        return Disp(Constant("n", All("m",Field("N"), All("D",Field("N"), All("J",Field("N"),body)))));
    }

    private static Formula LocalFormula()
    {
        Formula r = I("r"), m = I("m"), j = I("J"), a = I("A"), f = I("f"), n = I("n"), i = I("i");
        Formula degree = Seq(m,Plus,r);
        Formula hypothesis = All("n",Field("N"),Seq(n,Le,Sp,r,Rightarrow,Sp,
            All("i",Field("N"),Seq(i,Le,Sp,m,Land,Sp,i,Le,Sp,j,Land,Sp,j,Le,Sp,i,Plus,r,Rightarrow,Sp,
                Norm(Call("f",n,i)),Le,Sp,Fr(a,Pow(Call("R",m,Fr(j,degree)),n))))));
        Formula body = All("f",Seq(Field("N"),To,Sp,Field("N"),To,Sp,Field("C")),
            Seq(Par(hypothesis),Rightarrow,Sp,Norm(Call("C",degree,j,Call("Q",m,r,f))),Le,Sp,I("K"),Cdot, Sp,a));
        body = All("A",Field("R"),Seq(D(0),Le,Sp,a,Rightarrow,Sp,body));
        body = All("J",Field("N"),Seq(j,Le,Sp,degree,Rightarrow,Sp,body));
        body = All("m",Field("N"),Seq(D(0),Lt,Sp,m,Land,Sp,r,Le,Sp,m,Rightarrow,Sp,body));
        return Disp(Constant("r",body));
    }
}
