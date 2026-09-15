using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZumkellerBinaryGaussianEvaluationZeroMultipleOfFiveDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/zumkeller2007a131853");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A vanishing binary digit polynomial at the Gaussian unit has an argument divisible by five.",
        H("Zumkeller's Binary Gaussian Evaluation"),
        Blocks(
            Node("z", "The binary Gaussian evaluation", RecurrenceFormula(),
                "The definition is Nat.binaryRec 0 (fun b _ w => (if b then 1 else 0) "
                + "+ ⟨0, 1⟩ * w). Here bit b n = 2n + (if b then 1 else 0), so the "
                + "equations are exactly the OEIS A131851 recursion for the binary digit "
                + "polynomial evaluated at the Gaussian imaginary unit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("zumkeller_a131853", "Zumkeller's divisibility conjecture", TheoremFormula(),
                "Binary induction proves m ≡ Re z(m) + 2·Im z(m) (mod 5). The identity "
                + "uses the fact that the Gaussian unit behaves as 2 modulo 5 because "
                + "2 squared is congruent to minus one. Therefore z(m) = 0 forces m to be "
                + "divisible by five, including the case m = 0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a131853-binary-gaussian-evaluation-zero-multiple-of-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a131853-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula RecurrenceFormula()
    {
        var b = F.Id("b");
        var n = F.Id("n");
        var initial = Equal(Call("z", D(0)), D(0));
        var digit = Call("if", b, D(1), D(0));
        var gaussianUnit = Seq(Langle, D(0), Comma, Sp, D(1), Rangle);
        var recursion = Universal("b", Booleans(), Universal("n", Naturals(), Equal(
            Call("z", Call("bit", b, n)),
            Add(digit, Multiply(gaussianUnit, Call("z", n))))));
        return Disp(And(initial, Parenthesized(recursion)));
    }

    private static Formula TheoremFormula()
    {
        var m = F.Id("m");
        var vanishes = Equal(Call("z", m), D(0));
        var divisible = new Formula.Relation(
            D(5), FormulaRelationOperator.Divides, m);
        return Disp(Universal("m", Naturals(),
            new Formula.Logic(vanishes, FormulaLogicOperator.Implies, divisible)));
    }

    private static Formula Naturals() => F.Id("Nat");
    private static Formula Booleans() => F.Id("Bool");
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
