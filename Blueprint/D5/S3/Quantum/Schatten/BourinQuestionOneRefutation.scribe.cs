using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class BourinQuestionOneRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/BourinQuestionOneRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuantumContext/bourin2008matrixsubadditivity");
    private const string Question =
        "Let Φ : M_n → M_k be a positive linear map between the algebras of matrices of size n and k "
        + "and let F_n and F_k be the sets of non-expansive, positive operators in M_n and M_k respectively. "
        + "Does Φ⁻¹(F_k) ⊂ F_n imply ‖f ∘ Φ(M)‖ ≤ ‖Φ ∘ f(M)‖ for all M ≥ 0, all symmetric norms "
        + "and all non-negative concave functions on the positive half line?";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bourin's Question 1 has a negative answer for the Frobenius norm and the square-root function.",
        H("A positive map reflecting positive contractions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bourin-question-one-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Question 1"),
                StatementSource.FromAuthor(Disp(Equal(Named("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Bourin, arXiv:0805.1954v1, p. 3, Question 1: \"" + Question + "\"")),
                    Paragraph(Text("The matrices are complex, and 1 is the identity matrix. "
                        + "The order is the Loewner order. Non-expansive positive matrices are exactly "
                        + "the matrices X with 0 ≤ X and X ≤ 1; the preimage is taken in the entire matrix algebra. "
                        + "The type D5.S3.Quantum.Schatten.UINorm contains the norm laws and invariance under "
                        + "left and right multiplication by unitary matrices. Its field N evaluates the norm. "
                        + "The real function f is concave and nonnegative on [0,∞); cfc applies it by "
                        + "continuous functional calculus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bourin-question-one-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The Frobenius inequality fails"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take n = 1, k = 2, Φ(X) = Matrix.diagonal ![X 0 0, X 0 0 / 4], "
                    + "M = 1 and f = Real.sqrt. Positivity of the first diagonal entry reflects positivity, "
                    + "and the upper bound on that entry reflects the upper bound by 1. "
                    + "The functional-calculus values are Matrix.diagonal ![1, 1/2] and "
                    + "Matrix.diagonal ![1, 1/4]. Their Frobenius norm squares are 5/4 and 17/16, "
                    + "respectively, contradicting the proposed inequality.")),
                    Paragraph(Text("The Frobenius norm laws come from Matrix's Frobenius norm. "
                        + "Its two-sided unitary invariance follows from invariance of RHLinalg.frobSq "
                        + "and its equality with the squared Frobenius norm. The first block suffices "
                        + "to reflect positive contractions, whereas the square root increases the second "
                        + "weight from 1/4 to 1/2. This argument concerns Question 1; it makes no assertion "
                        + "about Question 2 or a restriction to the operator norm."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var phi = F.Id("Phi");
        var x = F.Id("X");
        var m = F.Id("M");
        var norm = F.Id("N");
        var f = F.Id("f");
        var t = F.Id("x");
        var positive = All(x, Mat(n), Imp(LE(D(0), x), LE(D(0), App(phi, x))));
        var preimage = Seq(new Formula.Power(phi, Seq(Minus, D(1))),
            Parenthesized(Contractions(k)));
        var reflects = new Formula.Relation(preimage, FormulaRelationOperator.SubsetOf,
            Contractions(n));
        var concave = App(Named("ConcaveOn"), Reals(), Call(Qualified("Set", "Ici"), D(0)), f);
        var nonnegative = All(t, Reals(), Imp(LE(D(0), t), LE(D(0), App(f, t))));
        var conclusion = LE(App(Seq(norm, Dot, F.Id("N")), Call("cfc", f, App(phi, m))),
            App(Seq(norm, Dot, F.Id("N")), App(phi, Call("cfc", f, m))));
        var functions = All(f, new Formula.TypeArrow(Reals(), Reals()),
            Imp(concave, Imp(nonnegative, conclusion)));
        var norms = All(norm, Call(Qualified("D5.S3.Quantum.Schatten", "UINorm"), k), functions);
        var matrices = All(m, Mat(n), Imp(LE(D(0), m), norms));
        var linearMap = Seq(Mat(n), Sp, To, Underscore, Grp(F.Id("l")),
            OpenBracket, Complexes(), CloseBracket, Sp, Mat(k));
        return All(n, Naturals(), All(k, Naturals(), All(phi, linearMap,
            Imp(positive, Imp(reflects, matrices)))));
    }

    private static Formula Contractions(Formula size)
    {
        var x = F.Id("X");
        return Seq(OpenBrace, x, Colon, Sp, Mat(size), Sp, Bar, Sp,
            Parenthesized(And(LE(D(0), x), LE(x, D(1)))), CloseBrace);
    }

    private static Formula Mat(Formula size) => Call("Matrix", Call("Fin", size), Call("Fin", size), Complexes());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq([.. owner.Split('.').SelectMany((part, i) =>
            i == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Call(Formula name, params Formula[] args) => App(name, args);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
