using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class GibbsStochasticSimpleSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/vomende2024diagonalizable");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every strictly positive Gibbs vector admits a column-stochastic matrix with simple complex spectrum.",
        H("A simple-spectrum Gibbs-stochastic matrix for every positive vector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("has-simple-eigenvalues"),
                DeclarationHandle.Create(Prefix + "HasSimpleEigenvalues"),
                H("Simple complex eigenvalues"),
                StatementSource.FromAuthor(Disp(SimpleEigenvaluesDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A real matrix P has only simple eigenvalues when the multiset of roots of its "
                    + "complex characteristic polynomial has no repeated element. The entrywise map "
                    + "algebraMap from the real numbers to the complex numbers, including its "
                    + "coercion to a function by DFunLike.coe, is displayed explicitly. "
                    + "The source defines a simple eigenvalue as one of algebraic multiplicity one "
                    + "in channel_diag_approx.tex, lines 123-125. Since the complex characteristic "
                    + "polynomial splits, this predicate says that all n roots are distinct; for n = 0 "
                    + "the polynomial is one and its root multiset is empty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Existence for every positive Gibbs vector"),
                StatementSource.FromAuthor(Disp(IffOf(Name("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural dimension n and every strictly positive real vector d, "
                    + "there is a real matrix P in thermalProcesses d with only simple complex eigenvalues. "
                    + "Here thermalProcesses is the set of column-stochastic matrices preserving d: "
                    + "each entry is nonnegative, each column sums to one, and Pd = d. The vector d "
                    + "need not be normalized, and zero dimension is included. This is the existence "
                    + "statement associated with the construction question in the source's Outlook, "
                    + "channel_diag_approx.tex, lines 509-513. The density consequence described by "
                    + "the source's Lemma lemma_hartfiel, lines 170-181, is a separate statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A reversible chain with simple spectrum"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "In dimension n = m + 1, let c = sum over j of d j and put g i = d i / c. "
                        + "Strict positivity gives c > 0 and g i > 0, and the sum of the coordinates "
                        + "of g is one. Indices i and j are adjacent when i.val + 1 = j.val or "
                        + "j.val + 1 = i.val. For distinct adjacent indices set P i j = g i / 2, "
                        + "and set every other off-diagonal entry to zero. Set P j j equal to one "
                        + "minus the sum of g k / 2 over indices k adjacent to j.")),
                    Paragraph(Text(
                        "There are no indices adjacent to themselves. In column j, the off-diagonal "
                        + "sum is exactly the sum subtracted from P j j, so each column sums to one. "
                        + "For a nonnegative vector g whose coordinates sum to at most one, that "
                        + "subtracted sum is at most half the total sum. Thus each diagonal entry "
                        + "is at least one half, and every off-diagonal entry is nonnegative.")),
                    Paragraph(Text(
                        "The entry formula gives detailed balance, (P i j)(g j) = (P j i)(g i), "
                        + "also at diagonal and nonadjacent positions. Summing over j and using "
                        + "the column sum at i proves Pg = g. Since d = c times g and matrix-vector "
                        + "multiplication commutes with scalar multiplication, Pd = d. For the "
                        + "normalized vector above, these facts give P in thermalProcesses d.")),
                    Paragraph(Text(
                        "Let D be diagonal with entry sqrt(g i), and let E be diagonal with entry "
                        + "(sqrt(g i)) inverse. Positivity gives DE = I. Put S = EPD. "
                        + "The identity Matrix.charpoly_mul_comm applied to (EP)D gives "
                        + "charpoly(S) = charpoly(D(EP)) = charpoly(P), using associativity and DE = I.")),
                    Paragraph(Text(
                        "To express S as a Jacobi matrix, let a i = P i i and define "
                        + "e i = sqrt(g i) times sqrt(g(next i)) divided by two, where next i "
                        + "has value min(i.val + 1, m). Each e at an index t.castSucc with t in Fin m "
                        + "is positive. Checking diagonal, upper-adjacent, lower-adjacent and "
                        + "nonadjacent entries gives S = jacobiMatrix m a e. The adjacent entries "
                        + "are sqrt(g i) times sqrt(g j) divided by two; the cancellation uses "
                        + "g i / sqrt(g i) = sqrt(g i).")),
                    Paragraph(Text(
                        "For a Jacobi matrix J = jacobiMatrix m a e with these nonzero adjacent "
                        + "coefficients, suppose Jv = mu times v and v at Fin.last m is zero. "
                        + "The symmetric outer product X = vv transpose satisfies "
                        + "JX = X diag(mu), where diag(mu) is the constant diagonal matrix. "
                        + "Compare X with the zero matrix using the endpoint-uniqueness theorem "
                        + "symmetric_jacobi_intertwiner_unique of ZeitlinSixJ.Inverse: both are "
                        + "symmetric intertwiners and their last diagonal entries agree. Hence "
                        + "X = 0, which implies v = 0.")),
                    Paragraph(Text(
                        "The real symmetric matrix J is Hermitian, so choose its orthonormal "
                        + "eigenvector basis. Every basis vector has a nonzero last coordinate by "
                        + "the preceding implication. If the eigenvalues at i and j agree, put "
                        + "x and y equal to their basis vectors, c equal to the last coordinate "
                        + "of y, and b equal to the last coordinate of x. Then c times x minus "
                        + "b times y is an eigenvector with zero last coordinate, and therefore "
                        + "vanishes. If i and j were distinct, its ith basis coefficient would "
                        + "give c = 0, contradicting the nonzero last coordinate of y. Thus the "
                        + "eigenvalue function on the basis indices is injective.")),
                    Paragraph(Text(
                        "The Hermitian characteristic polynomial splits over the real numbers, "
                        + "and its root multiset is the image of the basis indices under that "
                        + "eigenvalue function. Injectivity makes this multiset have no repetitions. "
                        + "The injective map algebraMap from the real numbers to the complex numbers "
                        + "preserves this property, and Matrix.charpoly_map identifies the resulting "
                        + "multiset with the roots of the complex characteristic polynomial of J.")),
                    Paragraph(Text(
                        "In dimension zero, take the identity matrix. It is column stochastic and "
                        + "fixes the empty vector; its characteristic polynomial is one, with no "
                        + "roots. Finally split n into zero or m + 1. In the positive-dimensional "
                        + "case choose the matrix P constructed from the normalized vector g. Its "
                        + "column stochasticity and preservation of d give membership in "
                        + "thermalProcesses d. Apply Matrix.charpoly_map, the equality of the "
                        + "characteristic polynomials of P and S, and S = jacobiMatrix m a e. "
                        + "The simple complex spectrum of J then proves HasSimpleEigenvalues P."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vom-ende-2024-gibbs-stochastic-simple-spectrum"),
                    ResolutionKind.Proved)))));

    private static Formula SimpleEigenvaluesDefinition() =>
        All("n", Naturals(), All("P", MatrixType(), IffOf(
            Apply(Name("HasSimpleEigenvalues"), V("P")),
            Apply(Qualified("Multiset", "Nodup"),
                Apply(Qualified("Polynomial", "roots"),
                    Apply(Qualified("Matrix", "charpoly"),
                        Apply(Qualified("Matrix", "map"), V("P"),
                            Apply(Qualified("DFunLike", "coe"),
                                Apply(Name("algebraMap"), Reals(), Complexes())))))))));

    private static Formula ClaimBody() => All("n", Naturals(),
        All("d", Arrow(FinOf(V("n")), Reals()),
            Imp(All("i", FinOf(V("n")), LT(Typed(D(0), Reals()), Apply(V("d"), V("i")))),
                Some("P", MatrixType(), And(
                    new Formula.Relation(V("P"), FormulaRelationOperator.MemberOf,
                        Apply(Name("thermalProcesses"), V("d"))),
                    Apply(Name("HasSimpleEigenvalues"), V("P")))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula FinOf(Formula size) => Apply(Name("Fin"), size);
    private static Formula MatrixType() => Apply(Name("Matrix"), FinOf(V("n")), FinOf(V("n")), Reals());
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
