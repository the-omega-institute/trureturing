using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class UhlmannDiagonalMajorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/uhlmann2023spectralmajorization");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive definite similarity in dimension seven defeats diagonal majorization.",
        H("Positive definite similarity need not give diagonal majorization"), Blocks(
            Entry("majorization", "Majorizes", "Majorization by a doubly stochastic matrix",
                MajorizesFormula(),
                "Section 3, page 5: \"An alternative definition is that x ≺ y if and only if\" "
                + "x = Sy (3.2), \"where S is a doubly-stochastic matrix, i.e., nonnegative with every row and column sum equal to unity.\" "
                + "Majorizes y x means x ≺ y. The vectors are real and indexed by Fin n; "
                + "doublyStochastic supplies the nonnegativity and both unit-sum conditions.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("unrestricted-assertion", "claim", "The unrestricted diagonal-spectrum assertion",
                Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "Section 4, page 7: \"However, the fact that such a construction does not generally exist for n > 6 does not necessarily imply that the diagonal-spectrum majorization relationship does not hold in general.\" "
                + "\"Empirical investigation may be able to provide sufficient evidence to justify a conjecture or, alternatively, empirical and/or analytical efforts may identify counterexamples that constrain such generalizations\" "
                + "The formula expresses the unrestricted assertion considered there: n ranges over all natural numbers, "
                + "P is real symmetric positive definite, and Matrix.diagonal d is any real diagonal matrix. "
                + "The entries of d are the spectrum of its similarity by P. No upper bound on n is imposed.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A seven-dimensional refutation",
                Disp(Seq(Neg, Parenthesized(ClaimBody()))),
                "In blocks of sizes 1, 1 and 5, take P = [[10,1,2eᵀ],[1,10,2eᵀ],[2e,2e,10I]], "
                + "where e has five entries equal to one, and take d = (1,20,2,2,2,2,2). "
                + "For coordinates (x,y,z), the quadratic form is "
                + "10∑ᵢ(zᵢ+(x+y)/5)²+(7/2)(x+y)²+(9/2)(x−y)². "
                + "It is positive for every nonzero vector: its vanishing would force x+y=x−y=0 and then every zᵢ=0. "
                + "The inverse has hub block [[8/63,1/63],[1/63,8/63]], hub-to-leaf entries −1/35, "
                + "and leaf block I/10+(2/175)eeᵀ. Exact multiplication gives "
                + "diag(P·Matrix.diagonal(d)·P⁻¹) = (64/63,1565/63,36/35,36/35,36/35,36/35,36/35). "
                + "Every entry is at least 64/63. Every row of a doubly stochastic matrix forms a convex combination, "
                + "so its product with this vector has every entry at least 64/63. It cannot have first entry 1. "
                + "This contradicts the displayed unrestricted assertion. The source's results with their dimensional "
                + "restriction and its constructions from factors satisfying the majorization property keep their stated scopes.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("uhlmann-2023-diagonal-majorization-question"),
                ResolutionKind.Refuted) : null);

    private static Formula MajorizesFormula()
    {
        Formula n = V("n"), y = V("y"), x = V("x"), s = V("S");
        return Disp(All("n", Nat(), All("y", Arrow(Call("Fin", n), Real()),
            All("x", Arrow(Call("Fin", n), Real()),
                Equal(Call("Majorizes", y, x), Parenthesized(
                    ExistsIn("S", Matrix(n), And(
                        Member(s, Call("doublyStochastic", Real(), Call("Fin", n))),
                        Equal(x, App(Qualified("Matrix", "mulVec"), s, y))))))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = V("n"), p = V("P"), d = V("d"), i = V("i");
        Formula similarity = Multiply(Multiply(p, App(Qualified("Matrix", "diagonal"), d)),
            new Formula.Power(p, new Formula.Negate(Num(1))));
        Formula diagonalVector = Seq(V("fun"), Sp, Parenthesized(Seq(i, Colon, Sp, Call("Fin", n))),
            Sp, Mapsto, Sp, App(Parenthesized(similarity), i, i));
        return All("n", Nat(), All("P", Matrix(n), Imp(
            App(Qualified("Matrix", "PosDef"), p),
            All("d", Arrow(Call("Fin", n), Real()),
                Call("Majorizes", Parenthesized(diagonalVector), d)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Matrix(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Real());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
