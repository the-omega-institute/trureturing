using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TavakoliMorelliIncompleteMUBDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/tavakolimorelli2024schmidttracenorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incomplete families of mutually unbiased bases obey the Schmidt-number correlation trace-norm bound of Tavakoli and Morelli's Conjecture 3.",
        H("Schmidt-number bounds for incomplete mutually unbiased bases"),
        Blocks(
            Paragraph(Text(
                "The operators, normalized kets, pure projectors, correlation table and "
                    + "SchmidtNumberLE predicate are those of TavakoliMorelliIncompleteEAM. "
                    + "Each unitary matrix supplies an orthonormal basis through its columns. "
                    + "The unitary group consists of square complex matrices U satisfying "
                    + "U adjoint times U = U times U adjoint = identity. The trace norm is "
                    + "the sum of singular values.")),
            Node("MUBFamily", "Families of mutually unbiased bases", FamilyFormula(),
                "Section V B uses m orthonormal bases in dimension d. The squared overlap of a column from one basis with a column from a distinct basis is 1/d. A family is represented by arbitrary unitary matrices with precisely these cross-basis overlaps; the first basis is unrestricted. The type itself imposes no positivity or incompleteness condition on d or m.", DescribeRole.Definition),
            Node("MUBFamily.ket", "Normalized basis columns", KetFormula(),
                "The a-th column of the l-th unitary is the underlying vector of this normalized ket. Unitarity supplies its normalization. A ket is determined by its underlying vector, so the displayed coordinate formula specifies it completely.", DescribeRole.Definition),
            Node("MUBFamily.effect", "The local rank-one projectors", EffectFormula(),
                "The outcome label is a pair consisting of a basis label and a column label. Its effect is the pure projector of that column, with no d/n scaling. The d projectors in each basis sum to the identity.", DescribeRole.Definition),
            Node("Qm", "The MUB joint-probability table", QmFormula(),
                "As in Section V B and Born's rule in Eq. (8), Qm is the md by md matrix of joint outcome probabilities from the two independently chosen local families. The correlation definition takes the real part of each trace and embeds it in the complex numbers. The complete collection across m bases is used without averaging over the basis labels.", DescribeRole.Definition),
            Node("claim", "Tavakoli–Morelli Conjecture 3", ClaimFormula(),
                "Section V B, Conjecture 3, Eq. (54), asserts the bound for a state of Schmidt number r and m less than d+1 bases. The statement takes positive d and m with m at most d, and r from one to d. It uses Schmidt number at most r, since the right side increases with r. The subtraction m-1 and the division in the bound are real arithmetic.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("tavakoli-morelli-mub-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The incomplete-MUB Schmidt-number bound"),
                StatementSource.FromAuthor(Disp(X("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H, subtract its scalar trace component. Mutual unbiasedness makes the trace-zero diagonal subspaces of distinct bases orthogonal. Their measurement projections obey Pythagoras, so the sum of their squared trace coordinates is at most the squared Hilbert–Schmidt norm of the centered H. Restoring the scalar component gives the second-moment bound tr(H squared) plus (m-1)/d times (tr H) squared. Dimension one is handled directly, since the trace-zero space is zero.")),
                    Paragraph(Text(
                        "For a pure bipartite state the singular value decomposition of its coefficient matrix gives a Gram factorization of the probability table. The columns of its two factors are vectorized rank-one effects sandwiched by the square roots of the Schmidt diagonal and the local unitaries, with transposed effects on the second side. Hilbert–Schmidt Hölder bounds the trace norm by the product of their Frobenius norms. The sum of squared Schmidt coefficients equals one, and their sum squared is at most r. The common second-moment estimate therefore gives alpha plus beta r with alpha = 1 and beta = (m-1)/d. Linearity of the probability table, together with the trace-norm triangle inequality and homogeneity for nonnegative weights, extends this to every finite convex mixture of Schmidt rank at most r. This is the shared second-moment theorem applied to the MUB projectors, and its bound is exactly claim."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("tavakoli-morelli-2024-conjecture-3-incomplete-mub-schmidt-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create("tavakoli-morelli-mub-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + (name == "MUBFamily.effect" ? "effect" : name == "MUBFamily.ket" ? "ket" : name)),
            H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Cast(X(name), type), Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula PairType(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Unitary() => Call("unitaryGroup", Fin(X("d")), Complex());
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Field(Formula value, string name) => Seq(Parenthesized(value), Dot, X(name));
    private static Formula Effect(Formula a) => Field(a, "effect");
    private static Formula Ket(Formula a, Formula l, Formula i) => At(Field(a, "ket"), l, i);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Square(Formula a) => new Formula.Power(Parenthesized(a), D(2));
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula LambdaOver(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Cast(X(name), type), Sp, Mapsto, Sp, body));
    private static Formula Dimensions(Formula body) => All("d", Nat(), All("m", Nat(), body));
    private static Formula FamilyInputs(Formula body) => Dimensions(All("A", Call("MUBFamily", X("d"), X("m")), body));

    private static Formula FamilyFormula()
    {
        var left = Field(At(X("U"), X("l")), "val");
        var right = Field(At(X("U"), X("k")), "val");
        var overlap = Square(new Formula.Norm(At(Mul(Call("conjTranspose", left), right), X("a"), X("b"))));
        var condition = All("l", Fin(X("m")), All("k", Fin(X("m")),
            Imp(NotEqual(X("l"), X("k")), All("a", Fin(X("d")), All("b", Fin(X("d")),
                Equal(overlap, new Formula.Fraction(D(1), Cast(X("d"), Real()))))))));
        var family = Seq(OpenBrace, X("U"), Colon, Sp, Arrow(Fin(X("m")), Unitary()),
            Sp, Mid, Sp, condition, CloseBrace);
        return Disp(Dimensions(Equal(Call("MUBFamily", X("d"), X("m")), family)));
    }

    private static Formula KetFormula()
    {
        var unitary = Field(At(Field(X("A"), "val"), X("l")), "val");
        return Disp(FamilyInputs(All("l", Fin(X("m")), All("a", Fin(X("d")),
            Equal(Field(Ket(X("A"), X("l"), X("a")), "vec"),
                LambdaOver("i", Fin(X("d")), At(unitary, X("i"), X("a"))))))));
    }

    private static Formula EffectFormula() => Disp(FamilyInputs(
        All("p", PairType(Fin(X("m")), Fin(X("d"))), Equal(At(Effect(X("A")), X("p")),
            Call("proj", Ket(X("A"), Call("fst", X("p")), Call("snd", X("p"))))))));

    private static Formula QmFormula() => Disp(Dimensions(
        All("rho", Call("BipartiteOp", X("d")), All("A", Call("MUBFamily", X("d"), X("m")),
            All("B", Call("MUBFamily", X("d"), X("m")), Equal(Call("Qm", X("rho"), X("A"), X("B")),
                Call("correlation", X("rho"), Effect(X("A")), Effect(X("B")))))))));

    private static Formula ClaimFormula()
    {
        var bound = Add(D(1), new Formula.Fraction(
            Mul(Parenthesized(Sub(Cast(X("m"), Real()), D(1))), Cast(X("r"), Real())), Cast(X("d"), Real())));
        var body = Dimensions(All("r", Nat(), Imp(Leq(D(1), X("d")), Imp(Leq(D(1), X("m")),
            Imp(Leq(X("m"), X("d")), Imp(Leq(D(1), X("r")), Imp(Leq(X("r"), X("d")),
                All("A", Call("MUBFamily", X("d"), X("m")), All("B", Call("MUBFamily", X("d"), X("m")),
                    All("rho", Call("BipartiteOp", X("d")), Imp(Call("SchmidtNumberLE", X("rho"), X("r")),
                        Leq(Call("traceNorm", Call("Qm", X("rho"), X("A"), X("B"))), bound))))))))))));
        return Disp(Iff(X("claim"), body));
    }
}
