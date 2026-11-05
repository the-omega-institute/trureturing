using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2017pfq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gamma product ratios and shifted Turanian coefficients.",
        H("The coefficient nonnegativity assertion"), Blocks(
            Entry("gamma-product-ratio", "coeff", "Gamma product ratios",
                "For vectors a of length p and b of length q, c(t) is the product of Gamma(a(i)+t) divided by the product of Gamma(b(j)+t). Empty products equal one, so a numerator vector of length zero is allowed."),
            Entry("shifted-turanian-coefficient", "turanCoeff", "The Cauchy coefficient",
                "For natural m, delta(m) is the sum over k from zero through m of [c(mu+alpha+k)c(mu+beta+m-k)-c(mu+k)c(mu+alpha+beta+m-k)] divided by k! times (m-k)!. Subtraction in the index m-k is natural subtraction; throughout this sum k is at most m. This is the coefficient in f(mu+alpha;x)f(mu+beta;x)-f(mu;x)f(mu+alpha+beta;x), where f(mu;x) has coefficient c(mu+n)/n! at degree n."),
            Entry("parameter-elementary-symmetric", "esymm", "Elementary symmetric functions",
                "The degree k elementary symmetric function is the sum of the products over all k-element selections of parameter positions. Repeated parameter values retain their multiplicities, and the degree zero value is one."),
            Describe.Lean(DescribeId.Create("constant-vector-elementary-symmetric"),
                DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/Defs.esymm_const"),
                H("Elementary symmetric functions of a constant vector"),
                StatementSource.FromAuthor(Disp(EsymmConstFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all natural n and k and every real x, the degree k elementary symmetric function of n copies of x is the real cast of n choose k times x to the power k. Every k-element subset contributes x to the power k, and there are n choose k such subsets. The identity includes k greater than n, when both sides vanish, and k zero, when both sides equal one. It supplies condition (13) for the repeated half parameters in both the coefficient and function counterexamples."))),
                DescribeRole.Theorem),
            Entry("symmetric-ratio-chain", "cond13", "The ratio chain",
                "For every natural j less than p, require e(q-j,b)/e(p-j,a) to be at most e(q-j-1,b)/e(p-j-1,a). With p at most q these are exactly the consecutive inequalities in the descending symmetric ratio chain. If p is zero there are no inequalities."),
            Entry("hypergeometric-coefficient-claim", "claim", "Universal coefficient nonnegativity",
                "For all p at most q and all positive parameter vectors satisfying the ratio chain, require delta(m) to be nonnegative for every natural m whenever mu is at least one, alpha and beta are nonnegative, and alpha is at most beta+1. This is the coefficient conclusion of the conjecture in the branch p at most q. Refuting this conclusion refutes the conjecture; no assertion about the value of the Turanian for nonnegative x is needed."),
            Lemma("gamma-three-halves", "gamma_three_halves", "Gamma at three halves",
                "Real.Gamma at 3/2 equals Real.sqrt Real.pi divided by 2. This is the natural-plus-half formula at one."),
            Lemma("gamma-five-halves", "gamma_five_halves", "Gamma at five halves",
                "Real.Gamma at 5/2 equals 3 times Real.sqrt Real.pi divided by 4. This is the natural-plus-half formula at two."),
            Lemma("gamma-seven-halves", "gamma_seven_halves", "Gamma at seven halves",
                "Real.Gamma at 7/2 equals 15 times Real.sqrt Real.pi divided by 8. This is the natural-plus-half formula at three."),
            Lemma("gamma-five-halves-reciprocal-power-product", "gamma_five_halves_inv_pow_mul",
                "The balanced reciprocal power product",
                "For every natural q, the product of two copies of the qth power of the reciprocal of Real.Gamma at 5/2 is (16/(9 pi))^q. Apply the Gamma value and the identity Real.sqrt Real.pi times itself equals Real.pi."),
            Lemma("gamma-three-seven-halves-reciprocal-power-product",
                "gamma_three_seven_halves_inv_pow_mul", "The outer reciprocal power product",
                "For every natural q, the product of the qth powers of the reciprocals of Real.Gamma at 3/2 and 7/2 is (16/(15 pi))^q. Apply the two Gamma values and the square-root identity."),
            Lemma("gamma-three", "gamma_three", "Gamma at three",
                "Real.Gamma at 3 equals 2, the factorial formula at two."),
            Lemma("gamma-two-three-reciprocal-power-product", "gamma_two_three_inv_pow_mul",
                "The integer reciprocal power product",
                "For every natural q, the product of the qth powers of the reciprocals of Real.Gamma at 2 and at 3 is (1/2)^q, since Real.Gamma at 2 is 1 and Real.Gamma at 3 is 2."),
            Lemma("base-power-times-half-power", "base_pow_mul_half_pow",
                "The base times one half",
                "For every natural q, (32/(9 pi))^q times (1/2)^q equals (16/(9 pi))^q."),
            Lemma("pi-exponential-base-bound", "pi_base_bound", "A rational lower bound for the base",
                "The inequality 640/567 < 32/(9 pi) follows from pi < 3.15 and positivity of pi. It supplies the common base estimate for the two negative coefficient families."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EsymmConstFormula()
    {
        var natural = Seq(Mathbb, Grp(V("N")));
        var real = Seq(Mathbb, Grp(V("R")));
        var constant = Seq(V("fun"), Sp,
            Parenthesized(Seq(V("i"), Colon, Sp, Call("Fin", V("n")))), Sp, Mapsto, Sp, V("x"));
        var choose = Parenthesized(Seq(new Formula.Apply(
            Seq(Operatorname, Grp(V("Nat"), Dot, V("choose"))), [V("n"), V("k")]), Colon, Sp, real));
        return All("n", natural, All("k", natural, All("x", real,
            new Formula.Relation(Call("esymm", Parenthesized(constant), V("k")), FormulaRelationOperator.Equal,
                new Formula.Binary(choose, FormulaBinaryOperator.Multiply,
                    new Formula.Power(V("x"), V("k")))))));
    }

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Lemma(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
