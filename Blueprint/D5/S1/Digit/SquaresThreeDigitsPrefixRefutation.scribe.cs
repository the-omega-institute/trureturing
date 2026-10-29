using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class SquaresThreeDigitsPrefixRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fifteen-block decimal word has a square with digits in {0,2,5}, "
            + "but deleting its last block gives a square containing digit one.",
        H("Prefix Closure Fails for Squares with Three Digits"),
        Blocks(
            Node("squares-three-digits-word", "The literal decimal word", "decimalWord",
                Disp(AllRuns(Eq(Call("decimalWord", F.Id("runs")),
                    Call("Append", Call("FlatMap", F.Id("block"), F.Id("runs")),
                        Call("Singleton", D(5)))))),
                "For each natural entry a, block(a) is the digit 4 followed by exactly "
                    + "a copies of 9. Concatenate those blocks in their listed order and "
                    + "append one final digit 5. Entries equal to zero produce a lone 4. "
                    + "This is the shorthand on page 25 of Geisser, Korner, Kurz and Zahn, "
                    + "Squares with three digits, arXiv:2112.00444v2.", DescribeRole.Definition),
            Node("squares-three-digits-value", "The ordinary decimal integer", "encode",
                Disp(AllRuns(Eq(Call("encode", F.Id("runs")), Call("ofDigits", D(1, 0),
                    Call("Reverse", Call("decimalWord", F.Id("runs"))))))),
                "Mathlib's Nat.ofDigits reads least significant digits first, so the "
                    + "literal decimal word is reversed exactly once. No polynomial "
                    + "surrogate or alternative digit predicate enters the definition.",
                DescribeRole.Definition),
            Node("squares-three-digits-predicate", "The actual square digits", "GoodSquare",
                Disp(AllNat("n", Iff(Call("GoodSquare", F.Id("n")), AllNat("d",
                    Implies(Call("In", F.Id("d"), Call("digits", D(1, 0),
                            new Formula.Power(F.Id("n"), D(2)))),
                        Or(Eq(F.Id("d"), D(0)),
                            Or(Eq(F.Id("d"), D(2)), Eq(F.Id("d"), D(5))))))))),
                "GoodSquare tests every digit of the ordinary natural integer square. "
                    + "It requires subset membership in {0,2,5}; it does not require "
                    + "that all three digits occur. The Boolean list test is true "
                    + "exactly when every digit satisfies that membership condition.",
                DescribeRole.Definition),
            Node("squares-three-digits-prefix-claim", "The whole prefix implication", "claim",
                Disp(Iff(F.Id("claim"), AllRuns(Implies(
                    new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual,
                        Call("length", F.Id("runs"))),
                    Implies(Call("GoodSquare", Call("encode", F.Id("runs"))),
                        Call("GoodSquare", Call("encode", Call("dropLast", F.Id("runs"))))))))),
                "Conjecture 1 on page 26 quantifies over every finite tuple of natural "
                    + "entries of length at least two. There is no bound on entries or "
                    + "length. Deletion removes the last entry and its entire 4/nines "
                    + "block; the final digit 5 remains.", DescribeRole.Definition),
            Node("squares-three-digits-counterexample", "A fifteen-block tuple", "counterexample",
                Disp(Eq(F.Id("counterexample"), Seq(OpenBracket,
                    D(0), Comma, D(1), Comma, D(3), Comma, D(7), Comma, D(1, 5), Comma,
                    D(3, 1), Comma, D(6, 3), Comma, D(1, 2, 7), Comma, D(2), Comma,
                    D(6), Comma, D(1, 4), Comma, D(6, 2), Comma, D(1, 4), Comma,
                    D(6), Comma, D(2), CloseBracket))),
                "The tuple is [0,1,3,7,15,31,63,127,2,6,14,62,14,6,2]. Its cumulative "
                    + "block lengths are 1,3,7,15,31,63,127,255,258,265,280,343,358,365,368. "
                    + "The full root has 369 decimal digits. Removing the final block "
                    + "leaves a root with 366 decimal digits.", DescribeRole.Definition),
            Node("squares-three-digits-prefix-refutation", "Prefix closure is false", "result",
                Disp(new Formula.Not(F.Id("claim"))),
                "The full tuple passes the literal square-digit test, while its dropLast "
                    + "tuple fails it. Both assertions are reduced by the Lean kernel. "
                    + "The implication at this tuple therefore contradicts claim. "
                    + "The carry mechanism can be seen from S, the cumulative lengths: "
                    + "N = 5*10^368*(1-sum(10^(-s),s in S)). Write S as "
                    + "{1,3,7,15,31,63,127} union (255+T), where "
                    + "T={0,3,10,25,88,103,110,113}. The four pairs "
                    + "(0,113),(3,110),(10,103),(25,88) have sum 113. In the normalized "
                    + "square they contribute four 5s in decimal position 624; their "
                    + "sum 20 carries a 2 into position 623. Deleting 113 leaves three "
                    + "such pairs, whose sum 15 carries a forbidden 1 instead. "
                    + "This refutes the entire universal implication; it makes no "
                    + "assertion of a least counterexample or historical priority.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula AllRuns(Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create("runs"),
            Seq(Operatorname, Grp(F.Id("List")), Grp(Seq(Mathbb, Grp(F.Id("N"))))))], body);

    private static Formula AllNat(string name, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))))], body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
}
