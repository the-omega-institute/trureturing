using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CuntzZeroFreeColumnRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CuntzZeroFreeColumnRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/cuntz2009integralmodulardata");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every zero-free column of an integral Fourier matrix consists of integer units.",
        H("Cuntz's zero-free column question"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourier-axioms"),
                DeclarationHandle.Create(Prefix + "FourierAxioms"),
                H("Integral Fourier matrix equations"),
                StatementSource.FromAuthor(Disp(FourierAxiomsFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Definition 4.1 (arXiv v2, pp. 8–9) starts: “Let s be an integral Fourier matrix, i.e. s ∈ ℤ^{n×n} and” and lists the four equations displayed here. Definition 3.1 (pp. 3–4) states: “Here, √dᵢ is chosen greater than 0.” The source indices 1,…,n are Fin n, with source index 1 represented by Fin.mk 0 hn. The matrix equation fixes d as the row norms; the explanatory reversed-index sum in Definition 3.1 is not an additional equation. Each structure constant is the displayed real sum equal to an integer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integral-fourier-matrix"),
                DeclarationHandle.Create(Prefix + "IsIntegralFourierMatrix"),
                H("Integral Fourier matrices"),
                StatementSource.FromAuthor(Disp(IntegralFourierMatrixFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Definition 4.1 (arXiv v2, pp. 8–9): “Let s be an integral Fourier matrix, i.e. s ∈ ℤ^{n×n} and” is followed by conditions (1)–(4). The real function d supplies the diagonal entries and positive square roots. Existence of a T-matrix and the later congruence conditions are not required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Section 7, Question (5)"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(Id("claim"), FormulaLogicOperator.Iff, ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Section 7(5) (arXiv v2, p. 21; journal p. 380): “Does an integral Fourier matrix s exist with a column k such that ∀i sᵢₖ ≠ 0 and ∃i sᵢₖ ≠ ±1?” The formula quantifies every positive size n, matrix s, column k and row i. The nonunit condition is the conjunction s i k ≠ 1 and s i k ≠ −1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The answer is negative"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For the real matrix A obtained from s, A A.transpose = Matrix.diagonal d implies that A.transpose times the inverse diagonal times A is one. Its diagonal entries give ∑ᵢ sᵢₖ²/dᵢ = 1. The first column gives ∑ᵢ 1/dᵢ = 1. Every nonzero integer square is at least one, and positivity of all reciprocal norms forces equality term by term. Thus every entry in a zero-free column is 1 or −1. The argument applies to any square integer matrix with first column one and positive orthogonal row norms; determinant, symmetrization and fusion integrality are unnecessary."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cuntz2009"),
                    ResolutionKind.Refuted)))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Id(owner)), Dot, Operatorname, Grp(Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Fin() => Call("Fin", Id("n"));
    private static Formula Matrix() => Call("Matrix", Fin(), Fin(), Ints());
    private static Formula Weights() => new Formula.TypeArrow(Fin(), Real());
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Real()));
    private static Formula Entry(Formula i, Formula j) => Call("s", i, j);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Positive(Formula value) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Some(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula And(params Formula[] clauses) => Seq(clauses.SelectMany((clause, index) =>
        index == 0 ? new[] { Parenthesized(clause) } : new[] { Land, Sp, Parenthesized(clause) }).ToArray());
    private static Formula SqrtAt(Formula index) => App(Q("Real", "sqrt"), Call("d", index));
    private static Formula MatrixCast() => App(Q("Matrix", "map"), Id("s"),
        Parenthesized(Seq(Q("Int", "cast"), Colon, Sp, new Formula.TypeArrow(Ints(), Real()))));

    private static Formula FourierAxiomsFormula()
    {
        var i = Id("i");
        var j = Id("j");
        var k = Id("k");
        var l = Id("l");
        var zero = App(Q("Fin", "mk"), D(0), Id("hn"));
        var fusionTerm = new Formula.Fraction(
            Mul(Mul(Cast(Entry(k, i)), Cast(Entry(k, j))), Cast(Entry(k, l))), Call("d", k));
        var sum = Seq(new Formula.Subscript(Sum, Seq(k, Colon, Sp, Fin())), Sp, Parenthesized(fusionTerm));
        var body = And(
            All("i", Fin(), Eqn(Entry(i, zero), D(1))),
            Ne(App(Q("Matrix", "det"), Id("s")), D(0)),
            All("i", Fin(), Positive(SqrtAt(i))),
            Eqn(Mul(MatrixCast(), App(Q("Matrix", "transpose"), MatrixCast())),
                App(Q("Matrix", "diagonal"), Id("d"))),
            All("i", Fin(), All("j", Fin(), Eqn(
                Mul(SqrtAt(j), Cast(Entry(i, j))), Mul(SqrtAt(i), Cast(Entry(j, i)))))),
            All("i", Fin(), All("j", Fin(), All("l", Fin(), Some("z", Ints(), Eqn(sum, Cast(Id("z"))))))));
        return All("n", Nat(), All("hn", Positive(Id("n")), All("s", Matrix(), All("d", Weights(),
            new Formula.Logic(Call("FourierAxioms", Id("hn"), Id("s"), Id("d")), FormulaLogicOperator.Iff, body)))));
    }

    private static Formula IntegralFourierMatrixFormula() =>
        All("n", Nat(), All("hn", Positive(Id("n")), All("s", Matrix(),
            new Formula.Logic(Call("IsIntegralFourierMatrix", Id("hn"), Id("s")), FormulaLogicOperator.Iff,
                Some("d", Weights(), Call("FourierAxioms", Id("hn"), Id("s"), Id("d")))))));

    private static Formula ClaimBody()
    {
        var i = Id("i");
        var k = Id("k");
        return Some("n", Nat(), Some("hn", Positive(Id("n")), Some("s", Matrix(),
            And(Call("IsIntegralFourierMatrix", Id("hn"), Id("s")),
                Some("k", Fin(), And(All("i", Fin(), Ne(Entry(i, k), D(0))),
                    Some("i", Fin(), And(Ne(Entry(i, k), D(1)), Ne(Entry(i, k), Seq(Minus, D(1)))))))))));
    }
}
