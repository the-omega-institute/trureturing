using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.RenyiSufficiency;

internal sealed class BouquetHolonomyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.",
        H("BouquetHolonomy"),
        Blocks(
            Node("transpose-state-invariance", "transpose state invariance", "transpose_state_invariance",
                Disp(All("U", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Imp(Seq(Parenthesized(Seq(Apply(Call("conjTranspose"), F.Id("U")), Sp, Times, Sp, Call("sigma"), Sp, Times, Sp, F.Id("U"))), Sp, Seq(Dot, Call("transpose")), Sp, Eq, Sp, Call("sigma")), Seq(Apply(Call("conjTranspose"), F.Id("U")), Sp, Times, Sp, Call("sigma"), Sp, Times, Sp, F.Id("U"), Sp, Eq, Sp, Call("sigma"))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("two-triangle-holonomy-obstruction", "two triangle holonomy obstruction", "two_triangle_holonomy_obstruction",
                Disp(All("U", Seq(Seq(Call("Matrix"), Dot, Call("unitaryGroup")), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Imp(Seq(Apply(Call("conjTranspose"), Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))))), Sp, Times, Sp, Call("sigma"), Sp, Times, Sp, F.Id("U"), Sp, Eq, Sp, Call("sigma")), Seq(Parenthesized(Seq(Call("rho"), Sp, Call("true"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))), Sp, Neq, Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Times, Sp, Call("rho"), Sp, Call("false"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))), Sp, Times, Sp, Apply(Call("conjTranspose"), Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))))))), Sp, Land, Sp, Parenthesized(Seq(Call("rho"), Sp, Call("true"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))), Sp, Neq, Sp, Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Times, Sp, Parenthesized(Seq(Call("rho"), Sp, Call("false"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Seq(Dot, Call("transpose")), Sp, Times, Sp, Apply(Call("conjTranspose"), Parenthesized(Seq(F.Id("U"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))))))))))),
                "Cancellation with the distinct diagonal weights and evaluation of the triangle entries exclude both conjugation orientations, providing the obstruction used by bouquet_not_interconvertible.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bouquet-not-interconvertible", "bouquet not interconvertible", "bouquet_not_interconvertible",
                Disp(Seq(Neg, Sp, Call("Interconvertible"), Sp, Parenthesized(Seq(Call("rho"), Sp, Call("false"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"), Sp, Parenthesized(Seq(Call("rho"), Sp, Call("true"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(1,0,0,0))))), Sp, Call("sigma"))),
                "Unitalizing positive trace-preserving interconversion would produce a positive inverse pair fixing the likelihood matrix. Its classification contradicts the two-triangle holonomy obstruction.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

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
