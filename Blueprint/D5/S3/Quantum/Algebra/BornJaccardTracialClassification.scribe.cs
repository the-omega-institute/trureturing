using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class BornJaccardTracialClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Born-weighted Jaccard distances on all complex subspaces are metrics exactly for tracial states.",
        H("Born-weighted Jaccard tracial classification"),
        Blocks(Describe.Lean(
            DescribeId.Create("born-jaccard-tracial-classification"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/BornJaccardTracialClassification."
                + "tracial_classification"),
            H("Full subspace classification and faithful separation"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let n be any integer at least two, H the usual complex Euclidean "
                    + "space of dimension n, rho any positive-definite Hermitian matrix of trace one, "
                    + "and c any nonnegative real number. All subspaces, projections and traces use "
                    + "this same H and rho. Write P(X) for the ordinary orthogonal projection onto X, "
                    + "mu(X)=Re Tr(rho P(X)), and f(X)=c+mu(X). The trace pairing is real. Join is "
                    + "the actual linear sum and meet is intersection. The distance d(X,Z) is "
                    + "1-f(X intersect Z)/f(X+Z) whenever its denominator is nonzero, and zero "
                    + "when the denominator vanishes. Faithfulness makes this last case exactly "
                    + "c=0 and X=Z=0.")),
                Paragraph(Text("The displayed Tri means the triangle inequality for every ordered "
                    + "triple of actual subspaces. The displayed Metric means that a MetricSpace "
                    + "structure exists on this full subspace type whose real distance is exactly d. "
                    + "It includes symmetry, nonnegativity and the zero diagonal. The final "
                    + "conjunct states separation for every faithful rho, including nonscalar rho. "
                    + "Coincident subspaces and all triples containing zero remain in scope.")),
                Paragraph(Text("For the scalar state, the projection trace theorem gives "
                    + "mu(X)=dim(X)/n. Dimension is monotone and modular. The positive-offset "
                    + "triangle bound directly applies BadicaJaccardArbitraryLattices.result; "
                    + "modularity supplies its log-submodularity hypothesis. Taking the right "
                    + "limit of positive offsets proves the zero-offset bound for each fixed "
                    + "triple. For a zero join the approximating distances are identically zero.")),
                Paragraph(Text("A nonscalar Hermitian operator has unequal eigenvalues M>m>0 "
                    + "on orthonormal vectors e and f. The actual lines spanned by 2e+f and "
                    + "2e-f have zero intersection and join span(e,f). Their common weight is "
                    + "(4M+m)/5 and their join has weight M+m. With the join as the middle "
                    + "subspace their triangle defect is 3(M-m)/(5(c+M+m)), strictly positive "
                    + "for every allowed c. The spectral theorem and trace one then give "
                    + "rho=I/n as the only all-triple case.")),
                Paragraph(Text("For separation, the difference of projections onto two strictly "
                    + "nested subspaces is an orthogonal projection onto a nonzero subspace. "
                    + "Its trace pairing with a faithful state is positive, so mu is strictly "
                    + "monotone. Equality of the meet and join weights therefore forces the "
                    + "two subspaces to coincide. These arguments formalize the tracial "
                    + "classification application in Corollary 4.1 of Born-weighted Jaccard "
                    + "projection geometry. They make no literature originality claim and "
                    + "do not include the separate sharp interval supremum or nonattainment "
                    + "assertions. All statements are general parameterized theorems, rather "
                    + "than finite computations or certified numerical instances."))),
            DescribeRole.Theorem),
            Paragraph(Text("For Corollary 4.2 use any index type I and the actual family P:I->End(H) of pairwise commuting "
                + "orthogonal projections. Pinned Mathlib LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute and "
                + "directSum_isInternal_of_pairwise_commute, in "
                + "Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean, accept arbitrary I; no finite-family "
                + "assumption is needed. Set H(chi)=the intersection of the eigenspaces of P(i) at chi(i). "
                + "orthogonalFamily_iInf_eigenspaces makes distinct such blocks orthogonal. Its independent nonzero "
                + "subfamily is finite by iSupIndep.fintypeNeBotOfFiniteDimensional, with at most n members by "
                + "iSupIndep.subtype_ne_bot_le_finrank in Mathlib/LinearAlgebra/Dimension/Finite.lean. These "
                + "interfaces use revision 56a005855ea17e0b0958f73ec801ae140b0a1679. The empty family and the "
                + "all-scalar family give one nonzero block H, and indistinguishable coordinates remain in the same "
                + "joint block.")),
            Paragraph(Text("Idempotence forces each chi(i) on a nonzero block to be 0 or 1. Each generator is consequently "
                + "the orthogonal sum of its 1-blocks. Finite sums, intersections and orthogonal complements of "
                + "these block sums correspond to union, intersection and complement of their index subsets, so "
                + "every event in the original generated Boolean algebra is such a sum. For the nonzero blocks set "
                + "p(chi)=weight rho H(chi). weight_pos and native_matrix_faithfulness give p(chi)>0. Repeated "
                + "weight_orthogonal_sup gives mu(event)=the sum of its p(chi), and the full sum is Tr(rho)=1. Thus "
                + "f_c on this same event algebra is nonnegative, monotone and modular. "
                + "modular_nonnegative_triangle applies for every c>=0, including its zero-pair branch; "
                + "faithful_separation, distance_properties restrict to the event algebra and give the remaining metric axioms. This "
                + "uses the one actual rho throughout, without any commutation of rho with the family. K1 Theorem 3 "
                + "also permits a nonnegative constant at the empty set; its citation is separate from the Lean "
                + "suppliers.")),
            Paragraph(Text("For Proposition 5.1, weight_orthogonal_sup is orthogonal additivity and weight_strictMono is "
                + "strict inclusion. In the scalar case the projection trace identity LinearMap.IsProj.trace and "
                + "Submodule.finrank_sup_add_finrank_inf_eq give full modularity. In the nonscalar case use the one "
                + "orthonormal eigenbasis from the spectral construction in operator_classification: equal "
                + "eigenvalues would give a scalar operator by basis extensionality and trace one, so some pair has "
                + "M>m>0. Apply BornJaccardFixedOverlap.pair_construction at any 0<r<1 to those two eigenvectors. "
                + "Its simultaneous line weights, actual zero meet and actual join T, together with "
                + "weight_orthogonal_sup, normalize to f_c(R+L)+f_c(R+N)-f_c(R+T)-f_c(R)=r(M-m)>0. This disproves "
                + "supermodularity and hence modularity. interval_defect gives positive triangle defect "
                + "r(M-m)/(c+mu(R)+M+m).")),
            Paragraph(Text("When n>=3, Fin.exists_ne_and_ne_of_two_lt supplies a third distinct index in that same "
                + "eigenbasis. Let R be its nonzero eigenline and T the span of the unequal-eigenvalue pair. "
                + "Orthonormality gives T<=R.orthogonal and dim(T)=2. At c=0, weight_pos gives mu(R)>0 and "
                + "weight_strictMono gives f_0(X)>=mu(R)>0 for every X in [R,R+T]. The same pair_construction and "
                + "interval_defect give the violation inside this strictly positive interval. When n=2 take R=0 and "
                + "T=H; the violation remains valid with the original zero-bottom convention. No representation "
                + "theorem for arbitrary two-dimensional measures is used. These are parameter choices in the "
                + "existing spectral and fixed-overlap suppliers, with no added theorem or enlargement of the "
                + "optimization domain.")),
            Paragraph(Text("For Proposition 5.2, LinearMap.IsProj.trace identifies the ordinary projector trace with dim(X). "
                + "scalar_triangle and modular_nonnegative_triangle supply the unweighted trace metric after "
                + "positive rescaling: c+dim(X) is n times c/n+dim(X)/n, so the quotient and zero-pair convention "
                + "agree; at c=0 normalized and ordinary trace give the same metric. Equation (1.4) retains its "
                + "strictly positive valuation hypotheses and the triangle substitutions described in "
                + "BadicaJaccardArbitraryLattices. Proposition 5.1 above identifies the modularity obstruction for "
                + "nonscalar Born weights, including the positive-bottom interval at n>=3, while the "
                + "commuting-event argument retains Corollary 4.2. The source references B1 and G1 are cited "
                + "inputs: Gleason's Theorem 4.1 concerns orthogonal additivity in separable real or complex "
                + "dimension at least three and a positive semidefinite trace-class representation. It supplies "
                + "neither arbitrary-pair modularity nor faithfulness. All metric and separation applications here "
                + "keep the finite faithful density hypotheses; no singular-state or infinite-dimensional "
                + "conclusion is inferred.")))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Statement()
    {
        var n = F.Id("n"); var rho = F.Id("rho"); var c = F.Id("c");
        var x = F.Id("X"); var z = F.Id("Z");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var space = new Formula.Power(complex, n);
        var scalar = Eqn(rho, new Formula.Fraction(F.Id("I"), n));
        var tri = Call("Tri", rho, c);
        var classification = Seq(Par(tri), Sp, Iff, Sp, Par(scalar));
        var separation = All("X", Call("Subspace", space), All("Z", Call("Subspace", space),
            Seq(Par(Eqn(Call("d", rho, c, x, z), D(0))), Sp, Iff, Sp, Par(Eqn(x, z)))));
        var hypotheses = And(Seq(D(2), Sp, Leq, Sp, n), And(Call("PosDef", rho),
            And(Eqn(Call("Tr", rho), D(1)), Seq(D(0), Sp, Leq, Sp, c))));
        return All("n", naturals, All("rho", Call("Matrix", n, n, complex),
            All("c", reals, Imp(hypotheses,
                And(classification, And(Imp(scalar, Call("Metric", rho, c)), separation))))));
    }
}
