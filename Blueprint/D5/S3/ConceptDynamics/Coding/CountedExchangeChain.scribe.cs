using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedExchangeChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedExchangeChain.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula A => F.Id("A");
    private static Formula C => F.Id("B");
    private static Formula L => F.Id("L");
    private static Formula Chain => F.Id("c");
    private static Formula X => F.Id("x");
    private static Formula Code(Formula x) => Call("applyHomeomorph", Call("chainCode", Chain), x);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("n", F.Id("Nat")), B("m", F.Id("Nat")),
             B("A", Call("CountMat", F.Id("n"), F.Id("n"))),
             B("B", Call("CountMat", F.Id("m"), F.Id("m"))), B("L", F.Id("Nat")),
             B("c", Call("ExchangeChain", F.Id("Nat"), A, C, L)), .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sequence of rectangular exchanges determines an actual conjugacy whose forward and inverse observation windows grow additively.",
        H("Counted matrix chains and bounded-window codes"),
        Blocks(
            Describe.Lean(DescribeId.Create("counted-chain-conjugacy-exists"),
                DeclarationHandle.Create(Prefix + "chain_has_window_conjugacy"), H("Construct the whole code"),
                StatementSource.FromAuthor(Disp(All(
                    Call("Nonempty", Call("WindowConjugacy", A, C, L))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The empty chain gives the identity. A nonempty chain composes the first counted-edge overlap homeomorphism with the recursively constructed tail. Every intermediate matrix size is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-chain-time-law"),
                DeclarationHandle.Create(Prefix + "chain_code_intertwines"), H("One time step for the entire chain"),
                StatementSource.FromAuthor(Disp(All(Equal(Code(Call("shift", A, X)),
                    Call("shift", C, Code(X))), B("x", Call("Path", A))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each elementary code preserves the same one-step shift. Their composition therefore preserves this time unit rather than passing to a higher power."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-chain-output-interval"),
                DeclarationHandle.Create(Prefix + "chain_full_window"), H("A finite output interval"),
                StatementSource.FromAuthor(Disp(Interval(false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("To recover outputs from a through b, input coordinates from a through b+L suffice. A code of window r followed by one of window s uses positions indexed by sums j+k, bounded by r+s."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-chain-input-interval"),
                DeclarationHandle.Create(Prefix + "chain_full_inverse_window"), H("The inverse observation interval"),
                StatementSource.FromAuthor(Disp(Interval(true))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse code recovers positions a through b from output positions a-L through b. The same homeomorphism supplies both recovery directions."))),
                DescribeRole.Theorem))));

    private static Formula Interval(bool inverse)
    {
        Formula a = F.Id("a"), b = F.Id("b"), i = F.Id("i"), y = F.Id("y");
        Formula lo = inverse ? new Formula.Binary(a, FormulaBinaryOperator.Subtract, L) : a;
        Formula hi = inverse ? b : new Formula.Binary(b, FormulaBinaryOperator.Add, L);
        Formula eq = Equal(Call("coordinate", X, i), Call("coordinate", y, i));
        Formula hypothesis = new Formula.BindMany(FormulaQuantifier.ForAll, [B("i", F.Id("Int"))],
            new Formula.Logic(Call("le", lo, i), FormulaLogicOperator.Implies,
                new Formula.Logic(Call("le", i, hi), FormulaLogicOperator.Implies, eq)));
        Formula cx = inverse ? Call("applyInverseHomeomorph", Call("chainCode", Chain), X) : Code(X);
        Formula cy = inverse ? Call("applyInverseHomeomorph", Call("chainCode", Chain), y) : Code(y);
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.ForAll, [B("i", F.Id("Int"))],
            new Formula.Logic(Call("le", a, i), FormulaLogicOperator.Implies,
                new Formula.Logic(Call("le", i, b), FormulaLogicOperator.Implies,
                    Equal(Call("coordinate", cx, i), Call("coordinate", cy, i)))));
        return All(new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion),
            B("x", Call("Path", inverse ? C : A)), B("y", Call("Path", inverse ? C : A)),
            B("a", F.Id("Int")), B("b", F.Id("Int")));
    }
}
