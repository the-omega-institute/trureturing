using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class MaityFuruichiDuttaOrderingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/MaityFuruichiDuttaOrderingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/maityfuruichidutta2026deformed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noncommuting positive definite qubit pair reverses the proposed Tsallis bound order.",
        H("The proposed noncommuting Tsallis bound order fails"),
        Blocks(
            Entry("logarithm", "lnr", "The deformed logarithm", Logarithm(),
                "Definition 1, printed p. 2: “The r-logarithm is denoted by ln_r(x) and it is defined by "
                + "ln_r(x) = (x^r − 1)/r, for r ≠ 0 and x ≥ 0.” The real power is Real.rpow.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("renyi", "renyiRZ", "The deformed Rényi relative entropy", Renyi(),
                "Definition 2, printed p. 2: “The r-deformed α-z-Rényi relative entropy for any two "
                + "positive semi-definite operators ρ and σ with Supp(ρ) ⊆ Supp(σ) is defined by "
                + "D^{(r)}_{α,z}(ρ||σ) = (1/(α−1)) ln_r Tr[(σ^{(1−α)/(2z)} ρ^{α/z} σ^{(1−α)/(2z)})^z] "
                + "… where α, r ∈ R and z ∈ R+.” The source calls this quantity B₁. "
                + "Here n is the dimension, rho and sigma are complex matrices, alpha denotes α, "
                + "cfc evaluates each real function of a Hermitian matrix, and re takes the real part of its trace.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("tsallis", "tsallis", "The Tsallis relative entropy", Tsallis(),
                "Equation (6), printed p. 2, gives D_α(ρ||σ) = Tr[ρ − ρ^α σ^{1−α}]/(1 − α). "
                + "The displayed expression uses cfc for the two matrix powers and the real part of the trace.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("second", "B2", "The second upper bound", SecondBound(),
                "Equations (8) and (47), printed pp. 2 and 11, give "
                + "B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})]. "
                + "Each real matrix function is evaluated by cfc, with the negative sign outside the real trace.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("ordering", "claim", "The source's proposed ordering", Claim(),
                "Equations (8)–(9), printed p. 2: “For 0 ≤ α < 1 and q > (1 − α), we compare two "
                + "upper bounds B₁(ρ||σ) = D^{(r)}_{α,z}(ρ||σ) and "
                + "B₂(ρ||σ) = −Tr[ρ ln_{1−α}((ρ^{−q/2} σ^q ρ^{−q/2})^{1/q})] of the Tsallis relative "
                + "entropy, numerically. We observe that for non-commutative density operators ρ and σ, "
                + "D_α(ρ||σ) ≤ B₁(ρ||σ) ≤ B₂(ρ||σ).” Section 4, Case 5, printed p. 12: "
                + "“Let Tr(ρ) = 1 and Tr(σ) = 1, that is both ρ and σ are density operators. Here, we "
                + "numerically observe that for any two operators ρ and σ, B₁(ρ||σ) is a tighter bound "
                + "of Tsallis relative entropy than B₂(ρ||σ).” "
                + "The formula ranges over every finite dimension. Positive definite matrices with unit trace "
                + "satisfy the support condition and admit negative powers. The parameters r≠0 and z>0 "
                + "come from Definitions 1–2. The function renyiRZ is precisely the source's B₁.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A noncommuting qubit counterexample",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take rho = diag(4/5,1/5) and sigma = (1/125)[[28,6√6],[6√6,97]]. "
                + "Both matrices are positive definite with unit trace, and they do not commute. "
                + "At alpha = r = 1/2, z = 2 and q = 1, the proof gives "
                + "2/5 < renyiRZ(alpha,r,z,rho,sigma) and B2(alpha,q,rho,sigma) < 2/5. "
                + "For the first value the trace inside the deformed logarithm is (2117+288√2)/3125, "
                + "so B₁ = 4(1−√((2117+288√2)/3125)). For the second, put "
                + "A = (1/25)[[7,3√6],[3√6,97]]. Its positive square root is "
                + "(5/√154)(A+1), giving B₂ = 2−20/√154. These inequalities contradict the second "
                + "conjunct of the proposed order. The inequality tsallis≤renyiRZ is not refuted here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("maity-furuichi-dutta-2026-tsallis-ordering-case-5"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Member(Formula value, string name) =>
        Seq(Parenthesized(value), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, Formula value) =>
        Seq(function, Sp, Parenthesized(value));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Different(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Negative(Formula value) => Seq(Minus, Sp, Parenthesized(value));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Mat => Call("Matrix", Call("Fin", V("n")), Call("Fin", V("n")), C);
    private static Formula Pair(Formula body) =>
        All("n", N, All("rho", Mat, All("sigma", Mat, body)));
    private static Formula Parameters(Formula body) =>
        All("alpha", R, All("r", R, All("z", R, body)));
    private static Formula PowerFunction(Formula exponent) => Parenthesized(Seq(
        Parenthesized(Seq(V("x"), Colon, Sp, R)), Sp, Mapsto, Sp, Pow(V("x"), exponent)));
    private static Formula MatrixPower(Formula matrix, Formula exponent) =>
        Call("cfc", PowerFunction(exponent), matrix);
    private static Formula RealTrace(Formula matrix) => Member(App(Qualified("Matrix", "trace"), matrix), "re");
    private static Formula RenyiValue => Call("renyiRZ", V("alpha"), V("r"), V("z"), V("rho"), V("sigma"));
    private static Formula SecondValue => Call("B2", V("alpha"), V("q"), V("rho"), V("sigma"));

    private static Formula Logarithm() => Disp(All("r", R, All("x", R,
        Eq(Call("lnr", V("r"), V("x")), Div(Sub(Pow(V("x"), V("r")), D(1)), V("r"))))));
    private static Formula Renyi()
    {
        var side = MatrixPower(V("sigma"), Div(Sub(D(1), V("alpha")), Mul(D(2), V("z"))));
        var middle = MatrixPower(V("rho"), Div(V("alpha"), V("z")));
        return Disp(Pair(Parameters(Eq(RenyiValue,
            Mul(Div(D(1), Sub(V("alpha"), D(1))),
                Call("lnr", V("r"), RealTrace(MatrixPower(Mul(Mul(side, middle), side), V("z")))))))));
    }
    private static Formula Tsallis() => Disp(Pair(All("alpha", R,
        Eq(Call("tsallis", V("alpha"), V("rho"), V("sigma")),
            Div(RealTrace(Sub(V("rho"), Mul(MatrixPower(V("rho"), V("alpha")),
                MatrixPower(V("sigma"), Sub(D(1), V("alpha")))))), Sub(D(1), V("alpha")))))));
    private static Formula SecondBound()
    {
        var side = MatrixPower(V("rho"), Negative(Div(V("q"), D(2))));
        var sandwich = Mul(Mul(side, MatrixPower(V("sigma"), V("q"))), side);
        var logarithm = Parenthesized(Seq(Parenthesized(Seq(V("x"), Colon, Sp, R)), Sp, Mapsto, Sp,
            Call("lnr", Sub(D(1), V("alpha")), V("x"))));
        return Disp(Pair(All("alpha", R, All("q", R, Eq(SecondValue,
            Negative(RealTrace(Mul(V("rho"), Call("cfc", logarithm,
                MatrixPower(sandwich, Div(D(1), V("q"))))))))))));
    }
    private static Formula ClaimBody()
    {
        var order = And(AtMost(Call("tsallis", V("alpha"), V("rho"), V("sigma")), RenyiValue),
            AtMost(RenyiValue, SecondValue));
        var parameters = Parameters(All("q", R,
            Imp(AtMost(D(0), V("alpha")), Imp(Less(V("alpha"), D(1)),
            Imp(Different(V("r"), D(0)), Imp(Less(D(0), V("z")),
            Imp(Less(Sub(D(1), V("alpha")), V("q")), order)))))));
        var noncommuting = Imp(Different(Mul(V("rho"), V("sigma")), Mul(V("sigma"), V("rho"))), parameters);
        return Pair(Imp(Member(V("rho"), "PosDef"), Imp(Eq(Member(V("rho"), "trace"), D(1)),
            Imp(Member(V("sigma"), "PosDef"), Imp(Eq(Member(V("sigma"), "trace"), D(1)), noncommuting)))));
    }
    private static Formula Claim() => Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff,
        Parenthesized(ClaimBody())));
}
