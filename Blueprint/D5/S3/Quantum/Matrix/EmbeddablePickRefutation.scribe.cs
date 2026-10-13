using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class EmbeddablePickRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/EmbeddablePickRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/johnson2026powersroots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive Pick function sends an embeddable stochastic matrix to a matrix with a negative entry.",
        H("Pick functions do not preserve embeddable matrices"),
        Blocks(
            SourceQuotation(),
            Entry("stochastic", "IsStochastic", "Stochastic matrices", Stochastic(),
                "A real n×n matrix is stochastic when every entry is nonnegative and every row sums to one.",
                DescribeRole.Definition, true),
            Entry("embeddable", "IsEmbeddable", "Embeddable stochastic matrices", Embeddable(),
                "Remark 3.28 characterizes embeddability by a real generator B with nonnegative off-diagonal "
                + "entries and zero row sums, whose exponential is A. The definition also requires stochasticity "
                + "and a unit determinant. Mathlib's NormedSpace.exp on matrices uses the product topology.",
                DescribeRole.Definition, true),
            Entry("preservation", "claim", "Preservation of embeddable matrices", Claim(),
                "The assertion uses the public pickFun and pickCalc definitions from the frozen companion "
                + "InfinitelyDivisiblePickRefutation. It quantifies over finite supports with b≥0, positive tᵢ, "
                + "nonnegative wᵢ, and strict positivity on every positive real argument. For every dimension n, "
                + "an embeddable upper-triangular matrix with positive diagonal must have an embeddable image. "
                + "Its spectrum is its diagonal and lies in (0,∞)⊂D; the positive shifts are invertible. "
                + "General preservation in Table 2, row 13, implies this restriction.",
                DescribeRole.Definition, false),
            Entry("refutation", "result", "A negative entry in dimension four", Disp(Seq(Neg, Sp, V("claim"))),
                "Let P have ones at (0,1), (1,2), (2,3), and (3,3), with every other entry zero. "
                + "Let Q have ones in its last column and zeros elsewhere. Exact multiplication gives P³=Q "
                + "and QP=Q; induction gives P^(k+3)=Q for every natural k. Splitting the exponential series "
                + "after degree two yields exp P=I+P+P²/2+(e−5/2)Q, where e=exp(1). Commutation with −I "
                + "gives A=exp(P−I)=e⁻¹(I+P+P²/2+(e−5/2)Q). The generator P−I has nonnegative off-diagonal "
                + "entries and zero row sums. The matrix A has nonnegative entries, unit row sums, and diagonal "
                + "(e⁻¹,e⁻¹,e⁻¹,1), so its determinant is e⁻³ and it is embeddable. It is upper triangular with "
                + "positive diagonal. Take a=1, b=0, t=(1), w=(1), giving f(z)=2z/(1+z)>0 for real z>0. "
                + "This is the finite-measure instance of Lemma 2.8. Its pole is outside D and its imaginary "
                + "part is 2 Im z/|1+z|², explaining the analytic Pick property without a separate formalization. "
                + "Writing d=1+e, an explicit right inverse C of A+I has rows "
                + "(e/d,−e/d²,e(1−e)/(2d³),(−e³+2e²+2e+1)/(2d³)), "
                + "(0,e/d,−e/d²,(1+2e−e²)/(2d²)), (0,0,e/d,(1−e)/(2d)), and (0,0,0,1/2). "
                + "The proof checks (A+I)C=I and identifies C as the inverse. Remark 2.9 gives f[A]=2I−2C, "
                + "whose (0,3) entry is (e³−2e²−2e−1)/(1+e)³<0, using certified bounds 2.718<e<2.72. "
                + "Thus the (1,4) entry in one-based indices is negative, the image is not stochastic, and "
                + "Table 2, row 13, has answer No. Rows 12 and 13 share the failure of entrywise positivity "
                + "under positive Pick functions on non-normal matrices. Row 7, semipositive matrices, remains open.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Johnson, Mondal, and Tsatsomeros, Powers, Roots, and Positivity, arXiv:2609.06298v1, "
        + "Table 2, Behavior of Matrix Classes under Pick Functions and Fractional Powers, p. 22, row 13, "
        + "verbatim: “Embeddable Matrix | Open | Yes”. The note below the table states verbatim: "
        + "“The entries marked Open indicate cases for which preservation under Pick functions remains an open question.” "
        + "Remark 3.28, p. 17, states verbatim: “The embedding problem, introduced in [11], asks whether a given "
        + "stochastic matrix A can be realized as the transition matrix of a continuous-time Markov process. "
        + "It was shown in [24] that a nonsingular stochastic matrix A is embeddable if and only if A = e^B "
        + "for some essentially nonnegative matrix B satisfying Be = 0.”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("johnson-mondal-tsatsomeros-2026-embeddable-pick-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Fin(string size) => Call("Fin", V(size));
    private static Formula Mat => Call("Matrix", Fin("n"), Fin("n"), Real);
    private static Formula Weights => Seq(Fin("k"), Sp, To, Sp, Real);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula At(string function) => Call(function, V("i"));
    private static Formula PickArgs(string function, params Formula[] rest) =>
        Call(function, [V("a"), V("b"), V("t"), V("w"), .. rest]);
    private static Formula Nonnegative(Formula a) =>
        All("i", Fin("n"), All("j", Fin("n"), Le(D(0), Call("entry", a, V("i"), V("j")))));


    private static Formula RowSum(Formula matrix, Formula value) => All("i", Fin("n"),
        Eq(Call("sum", V("j"), Fin("n"), Call("entry", matrix, V("i"), V("j"))), value));

    private static Formula Stochastic() => Disp(All("n", Nat, All("A", Mat,
        Iff(Call("IsStochastic", V("A")), And(Nonnegative(V("A")), RowSum(V("A"), D(1)))))));

    private static Formula Embeddable()
    {
        Formula generator = All("i", Fin("n"), All("j", Fin("n"),
            Imp(Seq(Neg, Sp, Parenthesized(Eq(V("i"), V("j")))),
                Le(D(0), Call("entry", V("B"), V("i"), V("j"))))));
        Formula exponential = Eq(Call("exp", V("B")), V("A"));
        Formula witness = Ex("B", Mat, And(generator, And(RowSum(V("B"), D(0)), exponential)));
        return Disp(All("n", Nat, All("A", Mat, Iff(Call("IsEmbeddable", V("A")),
            And(Call("IsStochastic", V("A")), And(Call("IsUnit", Call("det", V("A"))), witness))))));
    }

    private static Formula WithParameters(Formula body) => All("k", Nat,
        All("a", Real, All("b", Real, All("t", Weights, All("w", Weights, body)))));

    private static Formula Claim()
    {
        Formula output = Call("IsEmbeddable", PickArgs("pickCalc", V("A")));
        Formula triangular = All("i", Fin("n"), All("j", Fin("n"),
            Imp(Lt(V("j"), V("i")), Eq(Call("entry", V("A"), V("i"), V("j")), D(0)))));
        Formula diagonal = All("i", Fin("n"), Lt(D(0), Call("entry", V("A"), V("i"), V("i"))));
        Formula matrices = All("n", Nat, All("A", Mat, Imp(Call("IsEmbeddable", V("A")),
            Imp(triangular, Imp(diagonal, output)))));
        Formula positive = All("x", Real, Imp(Lt(D(0), V("x")), Lt(D(0), PickArgs("pickFun", V("x")))));
        return Disp(Iff(V("claim"), WithParameters(Imp(Le(D(0), V("b")),
            Imp(All("i", Fin("k"), Lt(D(0), At("t"))),
                Imp(All("i", Fin("k"), Le(D(0), At("w"))), Imp(positive, matrices)))))));
    }
}
