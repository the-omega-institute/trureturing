using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class HyperfiniteTypeII1FactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor.";
    private static LibraryNoteRef Borchers => LibraryNoteRef.Create("D5/L/HilbertOperators/borchers1992hsmi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The dyadic tracial bicommutant is a factor, with faithful normalized vacuum trace. " +
        "The minus-sided affine group acts unitarily on the Lebesgue Hilbert space.",
        H("Dyadic traces and minus-sided affine covariance"),
        Blocks(
            Result("normalized-trace-uniqueness", "normalizedTrace_unique", "Uniqueness of the normalized trace",
                "For positive matrix size, cyclicity kills off-diagonal matrix units and equates the values on diagonal units. "
                + "Normalization fixes their common value at the reciprocal of the matrix size. Linear expansion in matrix units determines the entire functional."),
            Result("trace-preservation", "normalizedTrace_embed", "Trace preserved by tensoring with the identity",
                "At level n, the algebra embedding sends a matrix to its Kronecker product with the two-dimensional identity. "
                + "Tensoring doubles the ordinary trace and the dimension. Reindexing preserves the diagonal sum.",
                All("n", Field("N"), All("a", Call("MatrixLevel", F.Id("n")),
                    Rel(Call("normalizedTrace", Seq(D(2), Caret, Grp(Seq(F.Id("n"), Sp, Plus, Sp, D(1)))),
                        Call("embed", F.Id("n"), F.Id("a"))), Eq,
                        Call("normalizedTrace", Seq(D(2), Caret, Grp(F.Id("n"))), F.Id("a")))))),
            Result("projection-unitary-equivalence", "projection_equiv_iff_trace", "Projection equivalence by normalized trace",
                "A Hermitian projection diagonalizes in a unitary eigenbasis. Idempotence gives only zero and one as eigenvalues. "
                + "The normalized trace counts the ones divided by the matrix size. Thus equal trace gives a common cutoff diagonal and a unitary conjugating one projection to the other. "
                + "Cyclicity gives the converse."),
            Result("algebraic-trace", "algTrace_spec", "Faithful normalized trace on the algebraic limit",
                "The compatible functionals descend to the direct limit. Products are computed in a common matrix algebra, where the finite trace is cyclic. "
                + "The trace of a star square is nonnegative and vanishes exactly when the element is zero."),
            Result("algebraic-center", "alg_center_iff", "Scalar center of the algebraic limit",
                "Represent a central element in one matrix algebra. Injectivity of the inclusion reflects commutation with that algebra's matrix units. "
                + "The off-diagonal entries then vanish and all diagonal entries agree."),
            Result("dyadic-projection-range", "alg_projection_trace_iff", "Exact projection dimensions in the algebraic limit",
                "A projection in the limit has a matrix representative that is itself a projection, by injectivity and preservation of star. "
                + "In dimension 2ⁿ, every integer rank from zero through 2ⁿ occurs as a diagonal cutoff and has normalized trace k/2ⁿ."),
            Result("dyadic-trace-closure", "dyadicTrace_closure", "Density in the unit interval",
                "For a real number in [0,1], divide the floor of its product with 2ⁿ by 2ⁿ. "
                + "The error lies between zero and 2⁻ⁿ, so these dyadic projection values converge to the given number."),
            Result("dyadic-vacuum-trace", "dyadicVacuumTrace_spec", "Faithful tracial vacuum functional",
                "Complete the algebra in the norm from its trace inner product and take the bicommutant of left multiplication. "
                + "Right multiplication commutes with it and its translates of the vacuum are dense, so the vacuum is separating. "
                + "The antiunitary extension of star sends the vector obtained from a bicommutant operator to the vector obtained from its adjoint. "
                + "This yields cyclicity, and the expectation of a star square is its vacuum norm squared."),
            Result("vacuum-trace-normal", "dyadicVacuumTrace_normal", "Normality of the vacuum trace",
                "For a bounded increasing positive net, each vector expectation increases to a finite limit. "
                + "The square of the norm of an operator increment on a vector is bounded by the scalar operator bound times the corresponding expectation increment. "
                + "This gives pointwise convergence to a bounded operator that still commutes with the centralizer. "
                + "The limit is the operator supremum, and evaluating it at the vacuum gives the supremum of the trace values."),
            Result("represented-matrix-tower", "representedMatrix_spec", "Faithful matrix inclusions in the bicommutant",
                "Left multiplication embeds each matrix algebra into the tracial bicommutant. "
                + "The inclusions are injective, preserve the trace, and are compatible with the forward embeddings."),
            Result("strong-density", "matrix_tower_strongly_dense", "Strong density of the increasing matrix algebras",
                "For any finite family of vectors, the closure of its orbit under diagonal left multiplication has an orthogonal projection. "
                + "Every matrix entry of this projection commutes with left multiplication, so a bicommutant operator preserves that orbit closure. "
                + "A single element of the algebraic limit approximates the operator on the whole finite family, and that element belongs to one matrix algebra."),
            Result("completed-projection-range", "completed_projection_trace_range", "All real projection dimensions in the unit interval",
                "For a given number in [0,1], the dyadic cutoff projections form an increasing sequence under the inclusions. "
                + "Its strong limit is a projection, and its trace is the limit of the dyadic dimensions. "
                + "Positivity of a projection and of its complement bounds every projection trace between zero and one."),
            Result("completed-center", "completed_center_iff", "Scalar center in the Hilbert completion",
                "For a central bounded operator z, the functional a ↦ ⟨Ω,z L(a)Ω⟩ on the algebraic limit is cyclic. "
                + "Subtract its value on the identity times the normalized trace. Uniqueness forces the difference to vanish. "
                + "Density and the separating vacuum then identify z with the corresponding scalar operator."),
            Result("minus-sided-action", "minusSidedAction_ae", "Minus-sided unitary operators",
                "For affine coordinates s and a, write λ=exp(−2πs). The unitary operator sends f to λ⁻¹ᐟ² f((x+a)/λ) almost everywhere. "
                + "The Jacobian of the affine coordinate change cancels the square of its normalization. The affine inverse gives the inverse unitary. "
                + "In exponential coordinates the same formula is exp(πs) f(exp(2πs)(x+a))."),
            Result("minus-sided-covariance", "minusSided_covariance", "Minus-sided affine covariance",
                "The group law sends pairs (s,a),(t,b) to (s+t,a+exp(−2πs)b). "
                + "Conjugating translation by dilation multiplies its parameter by exp(−2πs), which is at least one at nonpositive modular time. "
                + "The faithful real matrix representation has first row (exp(−2πs),a) and second row (0,1). "
                + "In Fourier coordinates the translation generator multiplies by 2πξ. On nonnegative frequencies its spectrum is the nonnegative real half-line. "
                + "On the common Schwartz domain the dilation and translation generators have commutator −2πiP.",
                acknowledgeBorchers: true)),
        []));

    private static DocumentBlock Result(string id, string name, string title, string prose,
        Formula? formula = null, bool acknowledgeBorchers = false) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
        acknowledgeBorchers ? AssessedProvenance.FromRepo(Borchers) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Rel(Formula a, Formula rel, Formula b) => Seq(a, Sp, rel, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
