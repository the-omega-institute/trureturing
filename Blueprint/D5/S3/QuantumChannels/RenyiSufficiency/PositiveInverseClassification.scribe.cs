using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.RenyiSufficiency;

internal sealed class PositiveInverseClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.",
        H("PositiveInverseClassification"),
        Blocks(
            Node("unital-positive-inverse-classification", "unital positive inverse classification", "unital_positive_inverse_classification",
                Disp(All("Phi", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Seq(new Formula.Subscript(To, F.Id("l")), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))), All("Psi", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Seq(new Formula.Subscript(To, F.Id("l")), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Imp(Seq(Call("IsPositive"), Sp, F.Id("Phi")), Imp(Seq(Call("IsPositive"), Sp, F.Id("Psi")), Imp(Seq(F.Id("Phi"), Sp, D(1), Sp, Eq, Sp, D(1)), Imp(Seq(F.Id("Psi"), Sp, D(1), Sp, Eq, Sp, D(1)), Imp(Seq(Seq(F.Id("Psi"), Dot, Call("comp")), Sp, F.Id("Phi"), Sp, Eq, Sp, Seq(Call("LinearMap"), Dot, Call("id"))), Seq(Exists, Sp, F.Id("U"), Sp, Colon, Sp, Seq(Call("Matrix"), Dot, Call("unitaryGroup")), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("Y"), Sp, Comma, Sp, F.Id("Phi"), Sp, F.Id("Y"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Times, Sp, F.Id("Y"), Sp, Times, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Lor, Sp, Parenthesized(Seq(Forall, Sp, F.Id("Y"), Sp, Comma, Sp, F.Id("Phi"), Sp, F.Id("Y"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Times, Sp, Seq(F.Id("Y"), Dot, Call("transpose")), Sp, Times, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))))))),
                "After aligning the diagonal projections, the Jordan identity confines each matrix unit to its two Peirce orientations. Their common orientation and phases produce a unitary or transpose-unitary conjugation.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Parenthesized(premise), Sp, Rightarrow, Sp, body);
}
