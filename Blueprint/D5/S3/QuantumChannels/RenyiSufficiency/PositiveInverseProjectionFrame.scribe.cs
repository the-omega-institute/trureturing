using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.RenyiSufficiency;

internal sealed class PositiveInverseProjectionFrameDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.",
        H("PositiveInverseProjectionFrame"),
        Blocks(
            Node("orthogonal-projection-frame", "orthogonal projection frame", "orthogonal_projection_frame",
                Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))), All("P", Seq(Call("Fin"), Sp, F.Id("n"), Sp, To, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Imp(Seq(Forall, Sp, F.Id("i"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("P"), Sp, F.Id("i"))), Sp, Seq(Dot, Call("IsHermitian"))), Imp(Seq(Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("P"), Sp, F.Id("i"), Sp, Neq, Sp, D(0)), Imp(Seq(Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("P"), Sp, F.Id("i"), Sp, Times, Sp, F.Id("P"), Sp, F.Id("i"), Sp, Eq, Sp, F.Id("P"), Sp, F.Id("i")), Imp(Seq(Forall, Sp, F.Id("i"), Sp, F.Id("j"), Sp, Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, To, Sp, F.Id("P"), Sp, F.Id("i"), Sp, Times, Sp, F.Id("P"), Sp, F.Id("j"), Sp, Eq, Sp, D(0)), Seq(Exists, Sp, F.Id("U"), Sp, Colon, Sp, Seq(Call("Matrix"), Dot, Call("unitaryGroup")), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("P"), Sp, F.Id("i"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Times, Sp, Call("single"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, D(1), Sp, Times, Sp, Apply(Call("conjTranspose"), Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))))),
                "Nonzero mutually orthogonal Hermitian projections give a unit vector in each range. These vectors form the columns of the unitary matrix U.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("positive-inverse-projection-alignment", "positive inverse projection alignment", "positive_inverse_projection_alignment",
                Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))), All("Phi", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Seq(new Formula.Subscript(To, F.Id("l")), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), All("Psi", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Seq(new Formula.Subscript(To, F.Id("l")), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Imp(Seq(Call("IsPositive"), Sp, F.Id("Phi")), Imp(Seq(Call("IsPositive"), Sp, F.Id("Psi")), Imp(Seq(F.Id("Phi"), Sp, D(1), Sp, Eq, Sp, D(1)), Imp(Seq(F.Id("Psi"), Sp, D(1), Sp, Eq, Sp, D(1)), Imp(Seq(Seq(F.Id("Psi"), Dot, Call("comp")), Sp, F.Id("Phi"), Sp, Eq, Sp, Seq(Call("LinearMap"), Dot, Call("id"))), Seq(Exists, Sp, F.Id("U"), Sp, Colon, Sp, Seq(Call("Matrix"), Dot, Call("unitaryGroup")), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("Phi"), Sp, Parenthesized(Seq(Call("single"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, D(1))), Sp, Eq, Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Times, Sp, Call("single"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, D(1), Sp, Times, Sp, Apply(Call("conjTranspose"), Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Parenthesized(premise), Sp, Rightarrow, Sp, body);
}
