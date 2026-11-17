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
            Export("rho", "Existing supporting declaration rho", "The rho supplies the common-basis application below."),
            Export("sigma", "Existing supporting declaration sigma", "The sigma supplies the common-basis application below."),
            Export("H", "Existing supporting declaration H", "The H supplies the common-basis application below."),
            Export("K", "Existing supporting declaration K", "The K supplies the common-basis application below."),
            Export("pair_states", "Existing supporting declaration pair_states", "The pair_states supplies the common-basis application below."),
            Export("pair_cfc", "Existing supporting declaration pair_cfc", "The pair_cfc supplies the common-basis application below."),
            Export("sandwich_trace", "Existing supporting declaration sandwich_trace", "The sandwich_trace supplies the common-basis application below."),
            Export("B1_gt", "Existing supporting declaration B1_gt", "The B1_gt supplies the common-basis application below."),
            Export("B2_lt", "Existing supporting declaration B2_lt", "The B2_lt supplies the common-basis application below."),
            Export("A", "Existing supporting declaration A", "The A supplies the common-basis application below."),
            Export("sandwich_A", "Existing supporting declaration sandwich_A", "The sandwich_A supplies the common-basis application below."),
            Export("A_nonneg", "Existing supporting declaration A_nonneg", "The A_nonneg supplies the common-basis application below."),
            Export("A_sqrt", "Existing supporting declaration A_sqrt", "The A_sqrt supplies the common-basis application below."),
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
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            NondiagonalApplication())));

    private static DocumentBlock NondiagonalApplication() => new DocumentBlock.Section(
        H("Application: both states nondiagonal in one common basis"),
        Blocks(
            Paragraph(Text("Haobo Ma and Wenlin Zhang's supplement, A Tsallis-bound counterexample with both states "
                + "nondiagonal (CC BY 4.0), answers Supriyo Dutta's common-basis question. Its source and license "
                + "are recorded in the accompanying Library note. Supriyo Dutta is distinct from Soumyojyoti Dutta "
                + "and Tushar. The following application uses the definitions and pair computations above; "
                + "it is a presentation of their consequences, not another conjecture resolution.")),
            new DocumentBlock.Section(H("The common orthogonal transformation and density matrices"), Blocks(
                Paragraph(Text("All displayed 2 by 2 matrices are complex matrices with real entries, indexed by Fin 2. "
                    + "Write X* for conjugate transpose and I for the identity. Set U = (1/√2)[[1,1],[1,−1]], "
                    + "ρ̂ = (1/10)[[5,3],[3,5]] and σ̂ = (1/250)[[125+12√6,−69],[−69,125−12√6]]. "
                    + "Because U is real symmetric and [[1,1],[1,−1]]² = 2I, U* = U and U² = I. "
                    + "Thus U is real orthogonal and, over the complex numbers, unitary.")),
                Paragraph(Text("For the existing ρ = diag(4/5,1/5) and σ = (1/125)[[28,6√6],[6√6,97]], "
                    + "multiplication gives UρU* = (1/10)[[5,3],[3,5]] = ρ̂ and "
                    + "UσU* = (1/250)[[125+12√6,−69],[−69,125−12√6]] = σ̂. "
                    + "The same U acts on both matrices. The existing pair_states supplies positive definiteness "
                    + "and trace one of ρ and σ. Unitary congruence preserves positive definiteness "
                    + "(Unitary.isUnit_coe and posDef_star_right_conjugate_iff), and cyclicity preserves trace. "
                    + "Therefore ρ̂ and σ̂ are positive definite density matrices. In particular, they are "
                    + "full rank, their supports agree, and their negative powers are defined spectrally.")),
                Paragraph(Text("Directly, Tr ρ̂ = 5/10+5/10 = 1 and Tr σ̂ = (125+12√6+125−12√6)/250 = 1. "
                    + "Their determinants are (25−9)/100 = 4/25 and "
                    + "(125²−(12√6)²−69²)/250² = (15625−864−4761)/62500 = 4/25. "
                    + "For either matrix, Matrix.charpoly_fin_two gives X²−X+4/25 = (X−4/5)(X−1/5), "
                    + "over the complex numbers. Hence each has the distinct eigenvalues 4/5 and 1/5, "
                    + "each with algebraic multiplicity one.")),
                Paragraph(Text("Both off-diagonal entries of ρ̂ are 3/10, and both off-diagonal entries of σ̂ "
                    + "are −69/250; all four entries are nonzero. Matrix multiplication gives "
                    + "[ρ̂,σ̂] = ρ̂σ̂−σ̂ρ̂ = (18√6/625)[[0,−1],[1,0]]. "
                    + "In particular [ρ̂,σ̂]₀₁ = −18√6/625 ≠ 0, since √6 > 0. "
                    + "Also [ρ̂,σ̂] = U[ρ,σ]U*, using U*U = I. Thus noncommutation is preserved, "
                    + "whereas the nonzero off-diagonal entries refer to this chosen common basis.")))),
            new DocumentBlock.Section(H("Covariance of the actual functional calculus"), Blocks(
                Paragraph(Text("More generally, for every natural n, every unitary u in Matrix (Fin n) (Fin n) ℂ, "
                    + "every real function f : ℝ → ℝ and every complex matrix X of that size, set "
                    + "e = Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) u, so e(X) = uXu*. "
                    + "Then e(cfc f X) = cfc f (e X). For self-adjoint X, use "
                    + "StarAlgHomClass.map_cfc with p = q = IsSelfAdjoint: finite_real_spectrum.continuousOn "
                    + "supplies continuity of any f on the finite real spectrum, and "
                    + "continuous_of_finiteDimensional supplies continuity of e. "
                    + "Self-adjointness is preserved by e. If X is not self-adjoint, injectivity of e "
                    + "reflects self-adjointness, so e X is not self-adjoint either; "
                    + "cfc_apply_of_not_predicate makes both cfc values zero, and map_zero completes the identity. "
                    + "No continuity assumption on f or positivity assumption on X is needed for this total-cfc identity.")),
                Paragraph(Text("For every such n and u, every pair ρ, σ of complex matrices, and every real α, r, z, q, "
                    + "the existing definitions satisfy renyiRZ α r z (e ρ) (e σ) = renyiRZ α r z ρ σ, "
                    + "B2 α q (e ρ) (e σ) = B2 α q ρ σ, and tsallis α (e ρ) (e σ) = tsallis α ρ σ. "
                    + "Indeed e preserves products and differences, and "
                    + "Tr(e X) = Tr(uXu*) = Tr(u*uX) = Tr X by Matrix.trace_mul_cycle and u*u = I. "
                    + "Apply the cfc identity to each real power and to x ↦ lnr (1−α) x, move e through "
                    + "the matrix products, then remove it under the trace. Real parts and the scalar factors "
                    + "in lnr, renyiRZ, B2 and tsallis are unchanged. These algebraic identities also cover "
                    + "the total definitions at singular or exceptional parameters; their entropy interpretation "
                    + "uses the source hypotheses stated above. In particular, for our U, "
                    + "cfc f (UXU*) = U(cfc f X)U* for every real f and every complex 2 by 2 X.")))),
            new DocumentBlock.Section(H("Source parameters and transported spectral quantities"), Blocks(
                Paragraph(Text("Take α = r = 1/2, z = 2 and q = 1. The source conditions are "
                    + "0 ≤ 1/2 < 1, r = 1/2 ≠ 0, z = 2 > 0 and q = 1 > 1−α = 1/2. "
                    + "Use B₁ = renyiRZ(1/2,1/2,2,ρ̂,σ̂), B₂ = B2(1/2,1,ρ̂,σ̂) and "
                    + "D = tsallis(1/2,ρ̂,σ̂), with exactly the existing definitions. "
                    + "The exponents (1−α)/(2z), α/z, z are respectively 1/8, 1/4, 2, "
                    + "and −q/2, q, 1/q are −1/2, 1, 1.")),
                Paragraph(Text("Define F = Re Tr[(σ̂^(1/8) ρ̂^(1/4) σ̂^(1/8))²], with every matrix power "
                    + "meaning cfc (x ↦ x^t), using Real.rpow. Covariance transports this entire expression "
                    + "to the original pair, so the existing sandwich_trace gives "
                    + "F = (2117+288√2)/3125. The same covariance and the existing sandwich_A give "
                    + "ρ̂^(−1/2) σ̂ ρ̂^(−1/2) = UAU*, where "
                    + "A = (1/25)[[7,3√6],[3√6,97]]. The existing A_nonneg and A_sqrt give "
                    + "A ≥ 0 and √A = (5/√154)(A+I); hence the square root of the transformed "
                    + "sandwich is U[(5/√154)(A+I)]U*. These are the actual spectral expressions "
                    + "inside the two bounds, not substituted scalar definitions.")))),
            new DocumentBlock.Section(H("Exact bound and Tsallis calculations"), Blocks(
                Paragraph(Text("Since lnr(1/2,x) = 2(√x−1) for x ≥ 0 and 1/(α−1) = −2, "
                    + "B₁ = 4(1−√F) = 4(1−√((2117+288√2)/3125)). For B₂, q = 1 removes "
                    + "the outer 1/q power, and the deformed logarithm is 2(√A−I). "
                    + "Direct evaluation with the existing ρ and A gives Tr(ρA) = 28/125+97/125 = 1, "
                    + "Tr ρ = 1 and Tr(ρ√A) = (5/√154)Tr(ρ(A+I)) = 10/√154. "
                    + "Consequently B₂ = −2 Re Tr[ρ(√A−I)] = 2−20/√154, "
                    + "with the same value for the hatted pair by simultaneous conjugation.")),
                Paragraph(Text("For D, apply the existing pair_cfc to f(x) = √x. Its values at the two "
                    + "eigenvalues are f(4/5) = 2/√5 and f(1/5) = 1/√5. "
                    + "With H = [[1,0],[0,−1]] and K = (1/25)[[−23,4√6],[4√6,23]], "
                    + "this gives √ρ = (3I+H)/(2√5) and √σ = (3I+K)/(2√5). "
                    + "Here Tr H = Tr K = 0 and Tr(HK) = −46/25. Thus "
                    + "Re Tr(√ρ√σ) = (18−46/25)/20 = 101/125. "
                    + "The existing tsallis definition now gives D = 2(1−101/125) = 48/125. "
                    + "Covariance gives this same value for ρ̂ and σ̂.")),
                Paragraph(Text("The existing B2_lt and B1_gt give B₂ < 2/5 < B₁. Explicitly, "
                    + "154 < (25/2)² gives √154 < 25/2 and hence B₂ < 2/5. "
                    + "Also √2 < 17/12 gives 0 < F < 2525/3125 = 101/125 < 81/100, "
                    + "so √F < 9/10 and B₁ > 2/5. To compare D with B₂, "
                    + "1250² = 1562500 < 1570954 = 154·101² implies √154 > 1250/101. "
                    + "Therefore 20/√154 < 202/125 and D = 48/125 < 2−20/√154 = B₂. "
                    + "Together D < B₂ < 2/5 < B₁, and in particular D < B₂ < B₁. "
                    + "Both displayed quantities are strict upper bounds for D at this pair.")))),
            new DocumentBlock.Section(H("Restricted comparison and scope"), Blocks(
                Paragraph(Text("Consider the universally quantified comparison over all complex 2 by 2 matrices "
                    + "ρ, σ with ρ.PosDef, Tr ρ = 1, σ.PosDef, Tr σ = 1, ρσ ≠ σρ, "
                    + "ρ₀₁ ≠ 0 and σ₀₁ ≠ 0: renyiRZ(1/2,1/2,2,ρ,σ) ≤ B2(1/2,1,ρ,σ). "
                    + "The pair ρ̂, σ̂ satisfies every hypothesis, whereas B₂ < B₁ contradicts that conclusion. "
                    + "Thus even this restriction to two states nondiagonal in the same basis is false. "
                    + "This is a consequence of the existing refutation and its common-basis application; "
                    + "it adds no independently asserted Lean theorem. It makes no assertion of an ordering "
                    + "at other parameters, refutes neither D ≤ B₁ nor the source's commuting comparison, "
                    + "and does not assert a physical preparation protocol, a resource advantage, "
                    + "or literature novelty. Nondiagonality is basis dependent; noncommutation "
                    + "and all three values are invariant under a simultaneous unitary change of basis."))))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("maity-furuichi-dutta-2026-tsallis-ordering-case-5"),
                ResolutionKind.Refuted) : null);

    private static DocumentBlock Export(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("support-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose)), Paragraph(Text("Complete Lean statement: " + Exact(name).Replace('\n', ' ').Replace('\r', ' ')))));

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
    private static string Exact(string name) => name switch
    {
        "rho" => "def rho : Matrix (Fin 2) (Fin 2) ℂ := !![4/5, 0; 0, 1/5]",
        "sigma" => "def sigma : Matrix (Fin 2) (Fin 2) ℂ := !![28/125, (6 * Real.sqrt 6 : ℝ) / 125;\n  (6 * Real.sqrt 6 : ℝ) / 125, 97/125]",
        "H" => "def H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]",
        "K" => "def K : Matrix (Fin 2) (Fin 2) ℂ := !![-23/25, (4 * Real.sqrt 6 : ℝ) / 25;\n  (4 * Real.sqrt 6 : ℝ) / 25, 23/25]",
        "pair_states" => "lemma pair_states : rho.PosDef ∧ rho.trace = 1 ∧\n    sigma.PosDef ∧ sigma.trace = 1 ∧ rho * sigma ≠ sigma * rho",
        "pair_cfc" => "lemma pair_cfc (f : ℝ → ℝ) :\n    cfc f rho = ((f (4/5) + f (1/5))/2) • (1:Matrix (Fin 2) (Fin 2) ℂ) +\n      ((f (4/5) - f (1/5))/2) • H ∧\n    cfc f sigma = ((f (4/5) + f (1/5))/2) • (1:Matrix (Fin 2) (Fin 2) ℂ) +\n      ((f (4/5) - f (1/5))/2) • K",
        "sandwich_trace" => "lemma sandwich_trace :\n    (trace (cfc (fun x:ℝ => x^(2:ℝ))\n      (cfc (fun x:ℝ => x^(1/8:ℝ)) sigma * cfc (fun x:ℝ => x^(1/4:ℝ)) rho *\n        cfc (fun x:ℝ => x^(1/8:ℝ)) sigma))).re =\n      (2117 + 288 * Real.sqrt 2) / 3125",
        "B1_gt" => "lemma B1_gt : (2/5:ℝ) < renyiRZ (1/2) (1/2) 2 rho sigma",
        "B2_lt" => "lemma B2_lt : B2 (1/2) 1 rho sigma < (2/5:ℝ)",
        "A" => "def A : Matrix (Fin 2) (Fin 2) ℂ := !![7/25, (3 * Real.sqrt 6:ℝ)/25;\n  (3 * Real.sqrt 6:ℝ)/25, 97/25]",
        "sandwich_A" => "lemma sandwich_A :\n    cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho * sigma *\n      cfc (fun x:ℝ => x^(-(1/2:ℝ))) rho = A",
        "A_nonneg" => "lemma A_nonneg : (0:Matrix (Fin 2) (Fin 2) ℂ) ≤ A",
        "A_sqrt" => "lemma A_sqrt : cfc (fun x:ℝ => x^(1/2:ℝ)) A =\n    (5 / Real.sqrt 154:ℝ) • (A + 1)",
        _ => throw new ArgumentException("Unknown source declaration", nameof(name))
    };

}
