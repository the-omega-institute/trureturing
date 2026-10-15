using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class QutritStochasticNonunitalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/QutritStochasticNonunitalRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/graydon2022stochastic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A completely positive trace-preserving qutrit map has the identity vector as a Choi eigenvector with eigenvalue one half, but does not preserve the identity matrix.",
        H("A stochastic qutrit channel that is not unital"), Blocks(
            Entry("stochastic", "IsStochastic", "Stochastic channels", StochasticFormula(),
                "Section II, page 2: \"A stochastic channel is a CPTP map Φ ∈ B(B(Cᵈ)) such that for some 0 < λ ≤ 1\" followed by Eq. (11), \"J(Φ)col(1_d) = λcol(1_d).\" "
                + "Here MatrixMap is the complex-linear matrix-map type, and IsCPTP is the completely positive trace-preserving predicate. The normalized Choi state is d⁻¹ times MatrixMap.choi_matrix Phi, with the cast of d to C shown explicitly. Its row (j,i) and column (k,l) entry is d⁻¹ Phi(Matrix.single i l 1)(j,k), so the output factor comes first. The identity vector has value one on equal indices and zero otherwise. Matrix.mulVec and scalar multiplication give exactly Eq. (11). The real parameter lam satisfies both strict positivity and the upper bound one. The expression also accepts d=0; the question below is at positive dimension three.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("question", "claim", "The qutrit unitality question", ClaimFormula(),
                "Section II, page 2: \"We leave open the question of whether or not all stochastic channels are unital for d = 3.\" "
                + "The universal quantifier ranges over every complex-linear map on 3 by 3 complex matrices. Stochasticity is Eq. (11) with complete positivity and trace preservation. Unitality is the equality Phi 1 = 1, where 1 is the identity matrix.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A nonunital stochastic qutrit channel", Disp(Seq(Neg, Sp, V("claim"))),
                "Take Kraus matrices I/√2, diag(1,−1/2,−1/2)/√2, √(3/8) Matrix.single 0 1 1, and √(3/8) Matrix.single 0 2 1, with zero-based indices. Their right Gram sum is the identity, giving trace preservation, and their Kraus sum is completely positive. The resulting channel acts by Phi(X)₀₀ = X₀₀ + (3/8)(X₁₁+X₂₂), by multiplication by 1/4 on entries with exactly one index zero, and by multiplication by 5/8 on the lower-right 2 by 2 block. Its normalized Choi state sends the identity vector to one half of that vector. Yet Phi(I) = diag(7/4,5/8,5/8), whose first diagonal entry differs from one. Thus the qutrit question has a negative answer. Appendix A's unitality theorem for stochastic qubit channels concerns dimension two.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("graydon-skanes-norman-wallman-2022-qutrit-stochastic-unitality"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula StochasticFormula()
    {
        Formula d = V("d"), phi = V("Phi"), lam = V("lam");
        Formula vector = Lambda("p", Pair(Fin(d), Fin(d)),
            Seq(V("if"), Sp, Equal(Projection(V("p"), 1), Projection(V("p"), 2)),
                Sp, V("then"), Sp, D(1), Sp, V("else"), Sp, D(0)));
        Formula choi = Lambda("p", Pair(Fin(d), Fin(d)), Lambda("q", Pair(Fin(d), Fin(d)),
            App(phi, App(Qualified("Matrix", "single"), Projection(V("p"), 2),
                Projection(V("q"), 2), D(1)), Projection(V("p"), 1), Projection(V("q"), 1))));
        Formula normalized = Scalar(new Formula.Power(Cast(d, Complex()), Negate(D(1))), choi);
        Formula eigen = Equal(App(Qualified("Matrix", "mulVec"), normalized, vector),
            Scalar(Cast(lam, Complex()), vector));
        Formula condition = And(Call("IsCPTP", phi), ExistsIn("lam", Real(),
            And(Less(D(0), lam), And(Le(lam, D(1)), eigen))));
        return Disp(All("d", Nat(), All("Phi", Map(d),
            Equal(Call("IsStochastic", phi), condition))));
    }

    private static Formula ClaimFormula() => Disp(Equal(V("claim"), All("Phi", Map(D(3)),
        Imp(Call("IsStochastic", V("Phi")), Equal(App(V("Phi"), D(1)), D(1))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Map(Formula d) => Call("MatrixMap", Fin(d), Fin(d), Complex());
    private static Formula Pair(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Projection(Formula value, byte digit) => Seq(value, Dot, D(digit));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Scalar(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula Negate(Formula value) => Seq(Minus, value);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
