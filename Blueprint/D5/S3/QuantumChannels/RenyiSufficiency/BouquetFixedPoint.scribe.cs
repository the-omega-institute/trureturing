using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.RenyiSufficiency;

internal sealed class BouquetFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.",
        H("BouquetFixedPoint"),
        Blocks(
            Node("mu-mul", "mu mul", "mu_mul",
                Disp(All("i", Seq(Call("Fin"), Sp, D(5)), All("j", Seq(Call("Fin"), Sp, D(5)), All("k", Seq(Call("Fin"), Sp, D(5)), All("l", Seq(Call("Fin"), Sp, D(5)), Seq(Parenthesized(Seq(Call("single"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Times, Sp, Parenthesized(Seq(Call("single"), Sp, F.Id("k"), Sp, F.Id("l"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Eq, Sp, Call("if"), Sp, F.Id("j"), Sp, Eq, Sp, F.Id("k"), Sp, Call("then"), Sp, Parenthesized(Seq(Call("single"), Sp, F.Id("i"), Sp, F.Id("l"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Call("else"), Sp, D(0))))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("jordan-projector-edge", "jordan projector edge", "jordan_projector_edge",
                Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))), All("i", Seq(Call("Fin"), Sp, F.Id("n")), All("j", Seq(Call("Fin"), Sp, F.Id("n")), Imp(Seq(F.Id("i"), Sp, Neq, Sp, F.Id("j")), All("Y", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Seq(Call("jordan"), Sp, Parenthesized(Seq(Call("single"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, D(1))), Sp, Parenthesized(Seq(Call("jordan"), Sp, Parenthesized(Seq(Call("single"), Sp, F.Id("j"), Sp, F.Id("j"), Sp, D(1))), Sp, F.Id("Y"))), Sp, Eq, Sp, F.Id("Y"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Cdot, Sp, Call("single"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, D(1), Sp, Plus, Sp, F.Id("Y"), Sp, F.Id("j"), Sp, F.Id("i"), Sp, Cdot, Sp, Call("single"), Sp, F.Id("j"), Sp, F.Id("i"), Sp, D(1)))))))),
                "The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bouquet-fixed-point-rigidity", "bouquet fixed point rigidity", "bouquet_fixed_point_rigidity",
                Disp(All("E", Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Seq(new Formula.Subscript(To, F.Id("l")), OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(5))), Sp, Seq(Mathbb, Grp(F.Id("C")))), Imp(Seq(Call("IsPositive"), Sp, F.Id("E")), Imp(Seq(F.Id("E"), Sp, D(1), Sp, Eq, Sp, D(1)), Imp(Seq(Forall, Sp, F.Id("Y"), Sp, Comma, Sp, Parenthesized(Seq(Call("sigma"), Sp, Times, Sp, F.Id("E"), Sp, F.Id("Y"))), Sp, Seq(Dot, Call("trace")), Sp, Eq, Sp, Parenthesized(Seq(Call("sigma"), Sp, Times, Sp, F.Id("Y"))), Sp, Seq(Dot, Call("trace"))), Imp(Seq(F.Id("E"), Sp, Parenthesized(Seq(Call("likelihood"), Sp, Call("false"))), Sp, Eq, Sp, Call("likelihood"), Sp, Call("false")), Seq(F.Id("E"), Sp, Eq, Sp, Seq(Call("LinearMap"), Dot, Call("id"))))))))),
                "The likelihood spectral projectors force trace preservation, which fixes sigma. Sigma projectors isolate the bouquet edges, and their Jordan closure generates every matrix unit.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

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
