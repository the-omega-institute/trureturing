using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class IntegerMutualReadoutDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/IntegerMutualReadout.";
    private static Formula X => F.Id("X");
    private static Formula R => F.Id("R");
    private static Formula K => F.Id("K");
    private static Formula E => F.Id("e");
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula All(Formula x, Formula t, Formula b) =>
        Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Open, a, Sp, Leftrightarrow, Sp, b, Close);
    private static Formula And(Formula a, Formula b) => Seq(a, Sp, Land, Sp, b);
    private static Formula Star(Formula a) => Seq(a, Caret, Grp(F.Star));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, b);
    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula SumOver(Formula i, Formula s, Formula b) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, s), Sp, b);
    private static Formula Recipe => Call("Finsupp", X, R);
    private static Formula Read(Formula f, Formula g) => Call("readout", E, K, f, g);
    private static Formula Budget(Formula e) => Call("Budget", e, K);
    private static Formula Frame(Formula b) => All(X, F.Id("Type"),
        All(K, Arrow(X, Arrow(X, C)), b));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On an arbitrary raw complex kernel, universal finite Gaussian-integer mutual-readout budgets are equivalent to rational and complex budgets and Hermitian positive type.",
        H("Integer mutual-readout budgets"),
        Blocks(
            Entry("mutual-kernel-readout", "readout", "The original finite comparison",
                ReadoutFormula(),
                "For any label type X, coefficient type R with zero, embedding e into the complex numbers and raw kernel K, readout is the finite double sum over the supports of f and g. The summand conjugates the first embedded coefficient and multiplies by the second without conjugation. No topology, norm, state, normalization or Hermitian condition on K is present.",
                DescribeRole.Definition),
            Entry("mutual-universal-budget", "Budget", "The unrestricted finite-recipe budget",
                BudgetFormula(),
                "Both recipes range over all finitely supported coefficient families on X. Supports have no common size bound and Gaussian-integer coefficients have no common magnitude bound; zero and empty recipes are retained. The three comparisons use the same K and the same scale.",
                DescribeRole.Definition),
            Entry("mutual-rational-coordinates", "rationalComplex", "Exact rational complex coordinates",
                All(F.Id("r"), Seq(Q, Sp, Times, Sp, Q),
                    Eq(Call("rationalComplex", F.Id("r")),
                        Seq(Call("fst", F.Id("r")), Sp, Plus, Sp,
                            Mul(Call("snd", F.Id("r")), F.Id("i"))))),
                "The pair (a,b) denotes a+b i, with a and b rational. These are precisely Q(i)=Q+iQ; the pair is a coordinate presentation of the coefficient set, and is not assigned the componentwise product-ring multiplication. Each finite recipe uses these exact embedded complex values.",
                DescribeRole.Definition),
            Entry("mutual-budget-positive-type", "mutual_budget_iff_positive_type",
                "All four conditions on the same raw kernel are equivalent",
                Frame(And(Iff(Budget(F.Id("toComplex")), Call("PosSemidef", K)),
                    And(Iff(Budget(F.Id("rationalComplex")), Call("PosSemidef", K)),
                        Iff(Budget(F.Id("id")), Call("PosSemidef", K))))),
                "This is C130 Theorem 2.3. X is arbitrary, including infinite and empty types, and K is any complex-valued table. Matrix.PosSemidef at this arbitrary index type asserts actual Hermitian symmetry of K and nonnegativity of every finitely supported complex quadratic form. Its existing submatrix theorem gives every finite indexed table, with arbitrary repeated labels and singular directions. Conversely, positivity of all finite tables recovers symmetry from two labels and each quadratic form from its finite support. Here toComplex denotes GaussianInt.toComplex. The equivalences each identify one of the integer, rational-coordinate and complex budgets with that same condition; no Hermitian premise is assumed.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "For each fixed finite subset of labels, Matrix.den and Matrix.num_div_den clear all rational real and imaginary denominators of both recipes at once. The positive square of that nonzero denominator cancels in the budget. Rat.denseRange_cast, DenseRange.piMap and closedness of the finite polynomial inequality extend the budget to all complex coefficients on that finite subset. This continuity is a theorem about coefficient space, with no topology on X and no physical-control assumption.")),
            Paragraph(Text(
                "The structural step uses the extended budget on t f and (t+i) f. Its difference is Re Q(f)+2t Im Q(f), for every real t. A nonzero imaginary part would allow an explicitly chosen t with negative difference. Thus self-comparisons are real; Mathlib's LinearMap.isSymmetric_iff_inner_map_self_real and Matrix.isSymmetric_toEuclideanLin_iff recover the original matrix's Hermitian symmetry. The zero-recipe test gives its nonnegative quadratic form. Conversely, Hermitian positive type makes the budget difference the nonnegative quadratic form of f-g. Restriction supplies both smaller coefficient domains.")),
            Paragraph(Text(
                "The raw readout is compared with finite subset tables through Finsupp.sum_of_support_subset, Finsupp.sum_embDomain and Finsupp.sum_fintype. The finite-subset argument retains the original entries of K throughout. Zero kernels, empty supports and null vectors require no division by a quadratic value or invertible Gram matrix. Formal recipe operations and coefficient approximation supply no physical copying, amplification, coherent preparation, measurement interface or physical continuity.")))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))), role);

    private static Formula ReadoutFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g"), x = F.Id("x"), y = F.Id("y");
        Formula term = Mul(Mul(Star(Apply(E, Apply(f, x))), Call("K", x, y)),
            Apply(E, Apply(g, y)));
        Formula body = All(f, Recipe, All(g, Recipe,
            Eq(Read(f, g), SumOver(x, Call("support", f),
                SumOver(y, Call("support", g), term)))));
        return All(X, F.Id("Type"), All(R, F.Id("Type"),
            Seq(OpenBracket, Call("Zero", R), CloseBracket, Comma, Sp,
                All(E, Arrow(R, C), All(K, Arrow(X, Arrow(X, C)), body)))));
    }

    private static Formula BudgetFormula()
    {
        Formula f = F.Id("f"), g = F.Id("g");
        Formula bound = Seq(Mul(new Formula.Number(2), Call("Re", Read(f, g))), Sp, Leq, Sp,
            Call("Re", Read(f, f)), Sp, Plus, Sp, Call("Re", Read(g, g)));
        return All(X, F.Id("Type"), All(R, F.Id("Type"),
            Seq(OpenBracket, Call("Zero", R), CloseBracket, Comma, Sp,
                All(E, Arrow(R, C), All(K, Arrow(X, Arrow(X, C)),
                    Iff(Budget(E), All(f, Recipe, All(g, Recipe, bound))))))));
    }
}
