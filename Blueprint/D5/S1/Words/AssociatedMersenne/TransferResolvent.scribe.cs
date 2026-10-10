using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AssociatedMersenne;

internal sealed class TransferResolventDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AssociatedMersenne/TransferResolvent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/wei2024associatedmersenne");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Degree enumeration for labelled circular run-constrained words.", H("TransferResolvent"), Blocks(
        Node("dMatrix", "dMatrix", Disp(All(Name("M"), Seq(Name("Matrix"), Sp, Parenthesized(Seq(Name("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Name("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Name("PowerSeries"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z")))))))), Seq(Name("dMatrix"), Sp, Name("M"), Sp, Eq, Sp, Parenthesized(Seq(Name("fun"), Sp, Name("i"), Sp, Name("j"), Sp, Mapsto, Sp, Parenthesized(Seq(Name("PowerSeries.derivative"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Parenthesized(Seq(Name("M"), Sp, Name("i"), Sp, Name("j")))))))), "Applying the power-series derivative to each matrix entry differentiates the transfer matrix.", DescribeRole.Definition),
        Node("matrixGeom", "matrixGeom", Disp(All(Seq(Name("i"), Sp, Name("j")), Seq(Name("Fin"), Sp, D(2)), Seq(Name("matrixGeom"), Sp, Name("i"), Sp, Name("j"), Sp, Eq, Sp, Name("PowerSeries.mk"), Sp, Parenthesized(Seq(Name("fun"), Sp, Name("n"), Sp, Mapsto, Sp, Sum, Sp, Name("k"), Sp, InMacro, Sp, Name("Finset.range"), Sp, Parenthesized(Seq(Name("n"), Sp, Plus, Sp, D(1))), Sp, Comma, Sp, Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Parenthesized(Seq(Parenthesized(new Formula.Power(Name("A"), Name("k"))), Sp, Name("i"), Sp, Name("j")))))))), "Each coefficient uses only powers k≤n, because A is divisible by PowerSeries.X³. All displayed sums are finite.", DescribeRole.Definition),
        Node("matrixGeom_inverse", "matrixGeom inverse", Disp(Seq(Parenthesized(Seq(D(1), Sp, Minus, Sp, Name("A"))), Sp, Cdot, Sp, Name("matrixGeom"), Sp, Eq, Sp, D(1))), "At each coefficient only finitely many powers contribute, and the finite geometric-sum identity gives the inverse.", DescribeRole.Theorem),
        Node("transferDet", "transferDet", Disp(Seq(Name("transferDet"), Sp, Eq, Sp, Parenthesized(Seq(Name("Matrix.det"), Sp, Parenthesized(Seq(D(1), Sp, Minus, Sp, Name("A"))))))), "The determinant of one minus the transfer matrix supplies the cleared transfer denominator.", DescribeRole.Definition),
        Node("transferTrace", "transferTrace", Disp(Seq(Name("transferTrace"), Sp, Eq, Sp, Parenthesized(Seq(Name("Matrix.trace"), Sp, Parenthesized(Seq(Name("matrixGeom"), Sp, Cdot, Sp, Name("dMatrix"), Sp, Name("A"))))))), "Tracing the matrix resolvent times the differentiated transfer matrix records marked cyclic paths.", DescribeRole.Definition),
        Node("transfer_trace_cleared", "transfer trace cleared", Disp(Seq(Name("transferDet"), Sp, Cdot, Sp, Name("transferTrace"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(Name("PowerSeries.derivative"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Name("transferDet"))), "Multiplying the resolvent by its determinant gives the adjugate and hence the negative determinant derivative.", DescribeRole.Theorem),
        Node("coeff_euler", "coeff euler", Disp(All(Name("f"), Parenthesized(Seq(Name("PowerSeries"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), All(Name("n"), Name("Nat"), Seq(Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Parenthesized(Seq(Parenthesized(Seq(Name("PowerSeries.X"), Sp, Colon, Sp, Name("PowerSeries"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Parenthesized(Seq(Name("PowerSeries.derivative"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Name("f"))), Sp, Eq, Sp, Parenthesized(Seq(Name("n"), Sp, Colon, Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Name("f"))))), "Multiplication by the length variable after differentiation multiplies the nth coefficient by n.", DescribeRole.Lemma),
        Node("trace_marked_coefficient", "trace marked coefficient", Disp(All(Name("ell"), Name("Nat"), All(Name("n"), Name("Nat"), Seq(Parenthesized(Seq(Parenthesized(Seq(Name("ell"), Sp, Plus, Sp, D(1), Sp, Colon, Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Parenthesized(Seq(Parenthesized(Seq(Name("PowerSeries.X"), Sp, Colon, Sp, Name("PowerSeries"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("Matrix.trace"), Sp, Parenthesized(Seq(new Formula.Power(Name("A"), Name("ell")), Sp, Cdot, Sp, Name("dMatrix"), Sp, Name("A"))))))), Sp, Eq, Sp, Parenthesized(Seq(Name("n"), Sp, Colon, Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Parenthesized(Seq(Name("Matrix.trace"), Sp, Parenthesized(new Formula.Power(Name("A"), Parenthesized(Seq(Name("ell"), Sp, Plus, Sp, D(1))))))))))), "Cyclic invariance of trace equates a marked matrix-power coefficient with its length-weighted derivative.", DescribeRole.Theorem),
        Node("coeff_euler_transferTrace", "coeff euler transferTrace", Disp(All(Name("n"), Name("Nat"), Seq(Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Parenthesized(Seq(Parenthesized(Seq(Name("PowerSeries.X"), Sp, Colon, Sp, Name("PowerSeries"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("transferTrace"))), Sp, Eq, Sp, Sum, Sp, Name("ell"), Sp, InMacro, Sp, Name("Finset.range"), Sp, Parenthesized(Seq(Name("n"), Sp, Plus, Sp, D(1))), Sp, Comma, Sp, Name("PowerSeries.coeff"), Sp, Name("n"), Sp, Parenthesized(Seq(Parenthesized(Seq(Name("PowerSeries.X"), Sp, Colon, Sp, Name("PowerSeries"), Sp, Parenthesized(Seq(Name("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Cdot, Sp, Name("Matrix.trace"), Sp, Parenthesized(Seq(new Formula.Power(Name("A"), Name("ell")), Sp, Cdot, Sp, Name("dMatrix"), Sp, Name("A")))))))), "Finite coefficient truncation expresses the marked resolvent trace as the sum of the length-weighted cyclic traces.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create("amg-transferresolvent-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Name(string name) {
        var parts = name.Split('.');
        Formula value = Word(parts[0]);
        for (var i = 1; i < parts.Length; i++) value = Seq(value, Dot, Word(parts[i]));
        return value;
    }
    private static Formula Word(string word) {
        if (word == "") return Sp;
        if (word == "0") return D(0);
        if (word == "1") return D(1);
        if (word == "2") return D(2);
        if (word.EndsWith("'", StringComparison.Ordinal)) return Seq(Word(word[..^1]), Apos);
        var parts = word.Split('_');
        Formula value = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++) value = new Formula.Subscript(value, Seq(Operatorname, Grp(F.Id(parts[i]))));
        return value;
    }
}
