using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class BlowUpMatchingAdjacencyTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/monterdepalkirkland2025blowup");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral adjacency support gives perfect state transfer at pi/2 after adding the same perfect matching in every clone set.",
        H("Adjacency transfer through uniform clone matchings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integral-support"),
                DeclarationHandle.Create(Prefix + "IntegralSupport"),
                H("Integral adjacency eigenvalue support"),
                StatementSource.FromAuthor(Disp(IntegralSupportFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "IntegralSupport g v says that every real eigenvalue l of the complex adjacency matrix "
                        + "having an eigenvector x with x(v) nonzero is an integer. The eigenvector equation "
                        + "includes l in the complex scalars; the conclusion includes an integer z in the reals. "
                        + "The source defines eigenvalue support by the nonzero spectral projection of a "
                        + "coordinate vector in main.tex, lines 156–158. Here that notion is applied to the "
                        + "adjacency matrix rather than the Laplacian: a nonzero projection onto a real "
                        + "eigenspace is equivalent to an eigenvector in that eigenspace with nonzero v-coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("blow-up-matching"),
                DeclarationHandle.Create(Prefix + "blowUpMatching"),
                H("The blow-up with a uniform matching perturbation"),
                StatementSource.FromAuthor(Disp(BlowUpMatchingFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The indices are pairs (vertex, clone). The first summand is the adjacency matrix "
                        + "of the n-fold blow-up: replace every vertex by n independent clones and every "
                        + "edge by all edges between the corresponding clone sets. The source gives this "
                        + "construction in main.tex, lines 126–128, with the clone coordinate first. "
                        + "The all-ones matrix is written as Matrix.of of two constant functions. "
                        + "The second summand repeats the permutation matrix of ρ in every clone set. "
                        + "The definition allows any permutation; when ρ is a fixed-point-free involution, "
                        + "this summand inserts the same perfect matching in every clone set. "
                        + "The permutation matrix sends a coordinate vector to its inverse image, "
                        + "which equals its image for an involution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Perfect state transfer across each matching edge above v"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let g be a finite simple graph, let v have integral adjacency eigenvalue support, "
                            + "and let 4 divide n. A fixed-point-free involution ρ on Fin n specifies a perfect "
                            + "matching of the clone indices. Adding this same perfect matching in every "
                            + "clone set gives adjacency perfect state transfer at π/2 between (v,j) and "
                            + "(v,ρ.val j) for every j. HasPST means that the squared modulus of the "
                            + "corresponding entry of exp(i t H) is one. No connectivity hypothesis is needed. "
                            + "The source asks about an appropriate matching in main.tex, line 814, following "
                            + "its Laplacian theorem at lines 666–668. The literal analogue with a matching "
                            + "only among the clones of v is not claimed.")),
                    Paragraph(Text(
                        "First, write n = 4q. For any integer z, exp(iπnz/2) = exp(2πi(qz)) = 1. "
                            + "Diagonalize the Hermitian adjacency matrix A of g as A = U D U*, with U a "
                            + "unitary eigenvector matrix and D the diagonal eigenvalue matrix. "
                            + "For an eigenvector whose v-coordinate vanishes, its contribution "
                            + "to the v-column vanishes. For every other eigenvector, IntegralSupport makes "
                            + "its real eigenvalue an integer, so the preceding phase identity applies. "
                            + "Thus every term of the v-column of U exp(iπnD/2) U* equals the corresponding "
                            + "term of U U*. Since U U* is the identity, exp(iπnA/2)eᵥ = eᵥ.")),
                    Paragraph(Text(
                        "Let J be the n by n all-ones matrix, put A₀ = A ⊗ J, "
                            + "and put B = I ⊗ P, where P is the permutation matrix of ρ.val. "
                            + "Both J P and P J equal J, since permuting rows or columns preserves J. "
                            + "The Kronecker multiplication identity therefore gives A₀ B = B A₀.")),
                    Paragraph(Text(
                        "For any complex square matrix b with b² = I, consider the complex algebra map "
                            + "from ℂ × ℂ to matrices that sends (a,d) to ((a+d)/2)I + ((a−d)/2)b. "
                            + "It sends (c,−c) to cb and commutes with the exponential, by continuity "
                            + "in finite dimension. At c = iπ/2 the two scalar exponentials are i and −i, "
                            + "so exp(iπb/2) = ib. The involutivity of ρ.val gives P² = I, and the "
                            + "Kronecker multiplication identity then gives B² = I. Consequently "
                            + "exp(iπB/2) = iB.")),
                    Paragraph(Text(
                        "Next J² = nJ gives, by induction on r, "
                            + "(A ⊗ J)^(r+1) = n^r (A^(r+1) ⊗ J). For n nonzero, apply the continuous "
                            + "coordinate evaluation maps to the convergent matrix exponential series. "
                            + "Every positive-degree coefficient agrees with n⁻¹ times the corresponding "
                            + "coefficient for exp((cn)A); the degree-zero coefficient supplies the identity "
                            + "correction. Uniqueness of the sums gives the following column formula: "
                            + "the p-coordinate of exp(cA₀)e_(v,k) is the p-coordinate of e_(v,k) "
                            + "plus n⁻¹ times the p.1-coordinate of exp((cn)A)eᵥ − eᵥ. "
                            + "Here n and n⁻¹ are interpreted in ℂ.")),
                    Paragraph(Text(
                        "The permutation-matrix action and involutivity give Be_(v,j) = e_(v,ρ.val j). "
                            + "The existence of j in Fin n ensures n is nonzero. With c = iπ/2, "
                            + "the periodicity of eᵥ makes the correction in the column formula zero, "
                            + "so exp(iπA₀/2) fixes e_(v,ρ.val j). Since A₀ and B commute, the "
                            + "exponential of their sum factors. Acting first by exp(iπB/2) = iB "
                            + "and then by exp(iπA₀/2) yields "
                            + "exp(iπ(A₀+B)/2)e_(v,j) = i e_(v,ρ.val j).")),
                    Paragraph(Text(
                        "Finally apply this column identity with ρ.val j in place of j "
                            + "and evaluate at (v,j). Involutivity gives ρ.val (ρ.val j) = j, "
                            + "so the matrix entry with row (v,j) and column (v,ρ.val j) equals i. "
                            + "The propagator at negative time −π/2 is exactly this positive-sign "
                            + "matrix exponential. Since Complex.normSq i = 1, the asserted HasPST follows."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("monterde-pal-kirkland-2025-blowup-matching-adjacency-transfer"),
                    ResolutionKind.Proved)))));

    private static Formula IntegralSupportFormula()
    {
        Formula eigenvector = Equal(
            At(Qualified("Matrix", "mulVec"), Adjacency(), X("x")),
            Smul(At(Qualified("Complex", "ofReal"), X("l")), X("x")));
        Formula integral = Some("z", Integers(),
            Equal(X("l"), Typed(At(Qualified("Int", "cast"), X("z")), Reals())));
        return GraphBinders(All("v", FinOf(X("m")),
            Equivalence(LocalCall("IntegralSupport", X("g"), X("v")),
                All("l", Reals(), All("x", Arrow(FinOf(X("m")), Complexes()),
                    Arrow(eigenvector,
                        Arrow(NotEqual(At(X("x"), X("v")), Typed(D(0), Complexes())), integral)))))));
    }

    private static Formula BlowUpMatchingFormula()
    {
        Formula multiplication = Typed(Qualified("HMul", "hMul"),
            Arrow(Complexes(), Arrow(Complexes(), Complexes())));
        Formula ones = At(Qualified("Matrix", "of"),
            At(Qualified("Function", "const"), FinOf(X("n")),
                At(Qualified("Function", "const"), FinOf(X("n")), Typed(D(1), Complexes()))));
        Formula blowUp = At(Qualified("Matrix", "kroneckerMap"), multiplication, Adjacency(), ones);
        Formula matching = At(Qualified("Matrix", "kroneckerMap"), multiplication,
            Typed(D(1), MatrixOf(FinOf(X("m")))),
            At(Qualified("Equiv", "Perm", "permMatrix"), Complexes(), X("ρ")));
        return GraphBinders(All("n", Naturals(), All("ρ", Permutations(FinOf(X("n"))),
            Equal(Typed(LocalCall("blowUpMatching", X("g"), X("n"), X("ρ")),
                    MatrixOf(PairType(FinOf(X("m")), FinOf(X("n"))))),
                Add(blowUp, matching)))));
    }

    private static Formula ResultFormula() => All("m", Naturals(), All("n", Naturals(),
        All("g", At(Qualified("SimpleGraph"), FinOf(X("m"))), InstanceBinder(
            All("v", FinOf(X("m")),
                All("ρ", At(Qualified("D5", "S3", "Zeros", "Convolution", "PerfectMatchingCount",
                        "FixedPointFreeInvolution"), FinOf(X("n"))),
                    Arrow(LocalCall("IntegralSupport", X("g"), X("v")),
                        Arrow(Seq(Typed(D(4), Naturals()), Sp, Mid, Sp, X("n")),
                            All("j", FinOf(X("n")),
                                At(Qualified("D5", "S3", "Quantum", "Dynamics", "RationalWeightPathTransfer",
                                        "HasPST"),
                                    LocalCall("blowUpMatching", X("g"), X("n"),
                                        At(Qualified("Subtype", "val"), X("ρ"))),
                                    new Formula.Fraction(Qualified("Real", "pi"), Typed(D(2), Reals())),
                                    Pair(X("v"), X("j")),
                                    Pair(X("v"), At(At(Qualified("Subtype", "val"), X("ρ")), X("j")))))))))))));

    private static Formula GraphBinders(Formula body) => All("m", Naturals(),
        All("g", At(Qualified("SimpleGraph"), FinOf(X("m"))), InstanceBinder(body)));
    private static Formula InstanceBinder(Formula body) => Seq(OpenBracket,
        At(Qualified("DecidableRel"), At(Qualified("SimpleGraph", "Adj"), X("g"))),
        CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Adjacency() => At(Qualified("SimpleGraph", "adjMatrix"), Complexes(), X("g"));
    private static Formula MatrixOf(Formula index) => At(Qualified("Matrix"), index, index, Complexes());
    private static Formula Permutations(Formula index) => At(Qualified("Equiv", "Perm"), index);
    private static Formula PairType(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula LocalCall(string name, params Formula[] args) => At(
        Qualified("D5", "S3", "Quantum", "Dynamics", "BlowUpMatchingAdjacencyTransfer", name), args);
    private static Formula X(string name) => name == "ρ" ? Rho : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Smul(Formula scalar, Formula vector) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(vector));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
