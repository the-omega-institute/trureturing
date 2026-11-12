using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HwangKimNearOrderRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/hwangkim2024nearorder");
    private static LibraryNoteRef BarycenterSource =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/bhatiajainlim2018wasserstein");
    private const string Question = "It would be an interesting problem to study whether the weak "
        + "log-majorization relation generalizes to the near-order or entrywise eigenvalue relation. "
        + "Note that (6.21) is a generalization of (4.14). From this point of view, we give an open question:";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive definite complex matrices refute the proposed near-order comparison of the log-Euclidean and Wasserstein means.",
        H("The log-Euclidean mean and Wasserstein near order"),
        Blocks(
            Entry("near-order", "NearOrder", "Near order", NearOrderFormula(),
                "Hwang and Kim, page 5, equation (3.5): “For A, B ∈ ℙ,” followed by “A ≼ B if and only if A⁻¹ # B ≥ I.” "
                + "Here matrices have indices Fin m, inverse means Matrix nonsingular inverse, "
                + "and geometricMean has weight 1/2. MatrixOrder is the positive semidefinite order.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("log-euclidean", "logEuclidean", "The log-Euclidean mean", LogEuclideanFormula(),
                "Page 9, equation (4.10), defines “exp [∑ⁿⱼ₌₁ wⱼ log Aⱼ] =: LE(ω; 𝔸).” "
                + "The finite index Fin n enumerates the n inputs; cfc applies Real.log and Real.exp to the matrices.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("bures-wasserstein-distance", "buresWassersteinDistance", "The Bures–Wasserstein distance", DistanceFormula(),
                "Page 4, Section 2: “where dW(A, B) = [tr(A + B) − 2 tr(A¹ᐟ² B A¹ᐟ²)¹ᐟ²]¹ᐟ² is the Bures-Wasserstein distance of A, B ∈ ℙₘ.” "
                + "SpectralPower.mpow is the real spectral power. Complex traces are read through Complex.re.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("wasserstein-barycenter", "wassersteinBarycenter", "The Wasserstein barycenter", BarycenterFormula(),
                "Bhatia, Jain and Lim, arXiv:1803.03357, page 1, equation (2): "
                + "“Let A₁, …, Aₘ be given positive definite matrices and let w = (w₁, …, wₘ) "
                + "be a vector of weights; i.e., wⱼ ≥ 0 and ∑ⱼ₌₁ᵐ wⱼ = 1. Then the (weighted) "
                + "Wasserstein mean, or the Wasserstein barycentre of A₁, …, Aₘ is defined as”. "
                + "Equation (2) displays Ω as the argmin of the weighted squared distances. "
                + "Here n counts the inputs and m is the matrix dimension; Fin n enumerates the inputs. "
                + "Classical.epsilon selects that minimizer. The formula below includes both positive definiteness "
                + "and comparison with every positive definite matrix.",
                AssessedProvenance.FromLiterature(BarycenterSource)),
            Entry("claim", "claim", "The final open inequality", Disp(Iff(V("claim"), ClaimBody())),
                "Hwang and Kim, arXiv:2407.07438v1, page 17, §6: “" + Question + "” "
                + "The following display is “LE(ω; 𝔸) ≼ Ω(ω; 𝔸).” "
                + "Here m is the complex matrix dimension, n is the number of inputs, w gives strictly positive "
                + "weights summing to one, and every A j is positive definite. Fin n replaces the source indices 1,…,n. "
                + "The assertion retains all dimensions m ≥ 1 and all input counts n ≥ 2.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("result", "result", "A counterexample in dimension two", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Take A = diag(4,1) and B = [[19,−3√15],[−3√15,61]]/64, at weights (1/2,1/2). "
                + "Both matrices are positive definite. Let L be their log-Euclidean mean and W their Wasserstein "
                + "barycenter. Their explicit formulas give det L = 1 and det W = d² with d > 0. "
                + "For C = geometricMean(1/2,L⁻¹,W), positivity and CLC = W imply det C = d. "
                + "If I ≤ C, positive semidefiniteness of C−I forces tr C ≤ 1+d. "
                + "Cayley–Hamilton trace identities then force "
                + "(tr W+d tr L)² ≤ (1+d)²(tr(LW)+2d), whereas rational bounds for √√2 and √265 "
                + "make the difference greater than 3/2500. The barycenter identity follows by minimizing "
                + "the actual sum of squared distances, using a trace-norm inequality with its equality condition. "
                + "The separate entrywise-eigenvalue question is not answered by this theorem.",
                AssessedProvenance.FromRepo(Source)),
            new DocumentBlock.Section(H("Complete revision2 companion scope"), CompanionScience()))));

    private static BlockSequence CompanionScience() => Blocks(
        Paragraph(Text(
            "Complete revision2 source: Counterexamples beyond Bhatia–Jain–Lim (2018): "
            + "Hwang–Kim's near-order question and its entrywise companion, Haobo Ma and Wenlin Zhang, "
            + "9 November 2026, CC BY 4.0. The whole TeX and provenance are retained through issue "
            + "#29594 and its complete-outcome plan. Haobo Ma: ChronoAI Pte Ltd, Singapore only. "
            + "Wenlin Zhang: National University of Singapore and ChronoAI Pte Ltd, Singapore. "
            + "The manuscript's historical Lean reference is commit 6974dba01daa1a25cc74b87a86c191e95fe2c681; "
            + "a source handoff or new formal package is not a new scientific discovery, publication or priority claim. "
            + "The original result above remains the universal near-order refutation. The separate "
            + "HwangKimStrictSpectralConverseRefutation.result proves that this same actual witness "
            + "also has strict domination of both decreasingly ordered eigenvalues, so the spectral converse fails.")),
        Paragraph(Text(
            "The finite dual lemma retains W,Aⱼ,Tⱼ positive definite, every wⱼ>0, Σwⱼ=1, "
            + "TⱼWTⱼ=Aⱼ and ΣwⱼTⱼ=I. The original fidelity inequality 2F(X,A)≤tr(TX)+tr(T⁻¹A) "
            + "has equality only if TXT=A. Summing the positive weighted gaps proves a global lower "
            + "bound attained at W. Equality makes each gap zero and one invertible transport forces X=W. "
            + "BuresWassersteinTransport.finite_barycenter_of_dual formalizes the lower bound for all X>0, "
            + "uniqueness and the actual epsilon-selected argmin. The established optimality condition "
            + "is due to Bhatia–Jain–Lim, arXiv:1712.01504v1 Theorem 8, (62)–(63), with Riccati equation (9). "
            + "This finite formal inference reuses the original private fidelity proofs.")),
        Paragraph(Text(
            "For arbitrary positive definite 2×2 L,W with det L=1, put d=√det W, s=tr W, t=tr L, "
            + "r=tr(LW), E=(s+dt)²−(1+d)²(r+2d), using real traces and determinant. "
            + "HwangKimTwoDimensionalCriterion.near_order_iff proves exactly NearOrder L W iff d≥1 and E≤0. "
            + "For the actual positive transport C=L⁻¹#W, CLC=W and det C=d; Cayley–Hamilton gives "
            + "s+dt=tr(LC)tr C and tr(LC)²=r+2d. Positivity gives tr(LC)>0, hence E≤0 iff tr C≤1+d. "
            + "Together with det C≥1, the positive eigenvalues c₁,c₂ obey (c₁−1)(c₂−1)≥0 and must both be ≥1. "
            + "The determinant condition and both positivity hypotheses are essential parts of the statement.")),
        Paragraph(Text(
            "The second written witness uses weights (3/4,1/4), A*=diag(256,1), "
            + "B*=[[13,3√3],[3√3,7]]/4. With h=√399, K*=[[9,2√3],[2√3,90]]/(4h) and "
            + "M*=(3I+K*)/4, K*A*K*=B* and the transports M*⁻¹,K*M*⁻¹ identify W*=M*A*M*. "
            + "Its trace is 1159/8+3591/(16h), and √det W*=73/8+297/(4h). "
            + "The source proves λmin(W*)<107/100<λmin(L*), where λmin(L*)=2^((13−√157)/4). "
            + "The exact bounds √157<63/5 and (107/100)^10<2 separate the logarithmic eigenvalue; "
            + "1997/100<h<999/50 makes the characteristic polynomial of W* at 107/100 smaller than −9/10. "
            + "HwangKimWeightedSpectralRefutation.result supplies the separate actual-mean entrywise refutation, "
            + "including both strict threshold bounds on its live proof path. A separate checked exact application also excludes near order for this same actual pair: C≥I implies C²≥I, so W−qI=C(L−qI)C+q(C²−I)≥0, contradicting its negative determinant. These are separate from the original result; "
            + "the source's finite checker alone is not a formal proof of them.")),
        Paragraph(Text(
            "The commuting finite-input outcome retains every strictly positive normalized weight. "
            + "In a single common unitary eigenbasis, write the positive coordinates aⱼₖ and "
            + "vₖ=Σⱼwⱼ√aⱼₖ. Then LE has coordinates ∏ⱼaⱼₖ^wⱼ and Ω has coordinates vₖ²; "
            + "Tⱼ=diag(√aⱼₖ/vₖ) supplies the actual barycenter certificate. Scalar weighted AM–GM "
            + "gives Loewner and near order; strict concavity of log makes equality equivalent to "
            + "all inputs coinciding. Bhatia–Jain–Lim (2018), equations (18) and (22), already publishes "
            + "the commuting formulas. An exact application check proves the displayed actual mean formulas, Loewner comparison and equality condition for arbitrary finite diagonal positive inputs by the finite transport certificate and existing scalar AM–GM. The full commuting-family application, simultaneous diagonalization, actual argmin "
            + "identification and the strict-positive-weight equality condition remain full formal obligations; "
            + "sorted spectra of individually diagonalized inputs do not supply a common basis.")),
        Paragraph(Text(
            "Both written counterexample families quantify over every matrix size m≥2 and every input "
            + "count n≥2, with suitable chosen strictly positive normalized weights, not every prescribed vector. "
            + "Direct sums with Iₘ₋₂ must be identified for the actual log-Euclidean, geometric and argmin means. "
            + "Repeat the first input n−1 times: assign weight 1/(2(n−1)) to each copy and 1/2 to the second "
            + "input in the first example, or 3/(4(n−1)) and 1/4 in the second. Logarithmic sums and objectives "
            + "then agree exactly with the two-input versions. Identity padding changes the full-size minimum "
            + "eigenvalues. For the second example, use the count of eigenvalues above q=107/100: "
            + "the L block has two and the W block has at most one; added identity eigenvalues lie below q. "
            + "Thus the separated sorted index is the second largest, not a claimed full-size minimum separator. "
            + "These direct-sum and repetition bridges are not consequences of merely negating a universal claim.")),
        Paragraph(Text(
            "The remaining reverse consequences use their established premises with attribution. "
            + "Bhatia–Jain–Lim (2018), Theorem 1 / (19), proves LE weakly log-majorized by Ω; "
            + "combined with the second witness this separates weak log-majorization from entrywise order. "
            + "Their (54) gives LE≤λQ₁/₂, where Q₁/₂=(ΣwⱼAⱼ¹/²)², and the same second witness obstructs "
            + "the unposed stronger entrywise Q₁/₂≤λΩ reading. Q₁/₂ is not Ω. Their actual Conjecture 1 / (25) "
            + "asks weak majorization, equivalently all unitarily invariant norms, and is not refuted. "
            + "Hiai arXiv:2508.20309v2 Propositions 4.6–4.7 compares binary weighted LE with the "
            + "quasi-arithmetic Aα,q; at q=1/2 the right side is Q₁/₂, not Ω. Gan–Huang's near-to-entrywise "
            + "implication is distinct from its spectral-geometric-versus-Wasserstein comparison. "
            + "For commuting X,Y, near and Loewner order agree coordinatewise in a common basis; "
            + "X=diag(2,1), Y=diag(1,2) shows that identical sorted spectra are insufficient.")),
        Paragraph(Text(
            "Source coverage is finite and exact: Hwang–Kim §6 p.17 final unnumbered question is the "
            + "original settled target; (6.21) is a different proved arithmetic–LE–harmonic comparison. "
            + "Their Theorem 6.1 and Corollary 6.2 Lie–Trotter assertions are prior results with no extension here. "
            + "The all-r analytic small-rotation family and full reverse-implication classification remain open. "
            + "The source's rational checker covers displayed identities and bounds for two specific witnesses; "
            + "it does not establish those open families. Primary-source access and priority are bounded by "
            + "the literature record in the source notes; unread journal/citing bodies and completeness of the "
            + "priority search remain unverified. No cited comparison is installed as an axiom. "
            + "The complete eight-group return is not certified by the original result, these exposition paragraphs, "
            + "a scoped build or a push; remaining actual consumers, admissibility audits, independent review "
            + "and final-head CI are separate obligations.")));


    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("hwang-kim-" + id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))), name == "result" ? DescribeRole.Theorem : DescribeRole.Definition,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hwang-kim-2024-near-order-log-euclidean-wasserstein"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        Seq(function, Parenthesized(Seq([.. args.SelectMany((arg, i) =>
            i == 0 ? new[] { arg } : new[] { Comma, Sp, arg })])));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", V("m")), Call("Fin", V("m")), Complex);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Half => new Formula.Fraction(D(1), D(2));
    private static Formula PosDef(Formula a) => App(Qualified("Matrix", "PosDef"), a);
    private static Formula ReTrace(Formula a) => App(Qualified("Complex", "re"), App(Qualified("Matrix", "trace"), a));
    private static Formula Sum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));

    private static Formula NearOrderFormula()
    {
        var mean = Call("geometricMean", Half, Pow(V("A"), new Formula.Negate(D(1))), V("B"));
        var body = Iff(Call("NearOrder", V("A"), V("B")), LeqF(D(1), mean));
        return Disp(All("m", Nat, All("A", Mat, All("B", Mat, body))));
    }
    private static Formula LogEuclideanFormula()
    {
        var summand = Seq(App(V("w"), V("j")), Sp, Cdot, Sp,
            Call("cfc", Qualified("Real", "log"), App(V("A"), V("j"))));
        var body = Eq(Call("logEuclidean", V("w"), V("A")),
            Call("cfc", Qualified("Real", "exp"), Sum("j", Call("Fin", V("n")), summand)));
        var inputs = All("w", Arrow(Call("Fin", V("n")), Real),
            All("A", Arrow(Call("Fin", V("n")), Mat), body));
        return Disp(All("m", Nat, All("n", Nat, inputs)));
    }
    private static Formula DistanceFormula()
    {
        var sandwich = Mul(Mul(Call("mpow", V("A"), Half), V("B")), Call("mpow", V("A"), Half));
        var distance = App(Qualified("Real", "sqrt"),
            Sub(ReTrace(Add(V("A"), V("B"))), Mul(D(2), ReTrace(Call("mpow", sandwich, Half)))));
        return Disp(All("m", Nat, All("A", Mat, All("B", Mat,
            Eq(Call("buresWassersteinDistance", V("A"), V("B")), distance)))));
    }
    private static Formula Objective(Formula x) => Sum("j", Call("Fin", V("n")),
        Mul(App(V("w"), V("j")), Pow(Call("buresWassersteinDistance", x, App(V("A"), V("j"))), D(2))));
    private static Formula BarycenterFormula()
    {
        var minimizing = All("Y", Mat, Imp(PosDef(V("Y")),
            LeqF(Objective(V("X")), Objective(V("Y")))));
        var selection = App(Qualified("Classical", "epsilon"),
            Lambda("X", Mat, And(PosDef(V("X")), minimizing)));
        var body = Eq(Call("wassersteinBarycenter", V("w"), V("A")), selection);
        var inputs = All("w", Arrow(Call("Fin", V("n")), Real),
            All("A", Arrow(Call("Fin", V("n")), Mat), body));
        return Disp(All("m", Nat, All("n", Nat, inputs)));
    }
    private static Formula ClaimBody()
    {
        var comparison = Call("NearOrder", Call("logEuclidean", V("w"), V("A")),
            Call("wassersteinBarycenter", V("w"), V("A")));
        var matrices = All("A", Arrow(Call("Fin", V("n")), Mat),
            Imp(All("j", Call("Fin", V("n")), PosDef(App(V("A"), V("j")))), comparison));
        var total = Eq(Sum("j", Call("Fin", V("n")), App(V("w"), V("j"))), D(1));
        var weights = All("w", Arrow(Call("Fin", V("n")), Real),
            Imp(All("j", Call("Fin", V("n")), Lt(D(0), App(V("w"), V("j")))), Imp(total, matrices)));
        return All("m", Nat, Imp(LeqF(D(1), V("m")),
            All("n", Nat, Imp(LeqF(D(2), V("n")), weights))));
    }
}
