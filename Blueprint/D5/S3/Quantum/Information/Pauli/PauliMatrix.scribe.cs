using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.Pauli;

internal sealed class PauliMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/Pauli/PauliMatrix.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/mahmoud2026macwilliams");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The single-qubit Pauli labels and matrix representation.",
        H("Pauli matrices"),
        Blocks(
            Node("pauli", "Pauli labels", PauliFormula(),
                "The four single-qubit Pauli labels.",
                "Pauli", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pauli-matrix", "Pauli matrices", PauliMatrixFormula(),
                "The label I gives the identity, X and Z give the frozen Pauli matrices qubitX and qubitZ, and Y gives i X Z, where i is the imaginary unit, so that Y has rows (0, -i) and (i, 0).",
                "pauliMatrix", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("mahmoudlu-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula PauliFormula() => Disp(Equal(Named("Pauli"),
        new Formula.SetLiteral([Named("I"), Named("X"), Named("Y"), Named("Z")])));

    private static Formula PauliMatrixFormula()
    {
        Formula Image(string label) => Call("pauliMatrix", Named(label));
        return Disp(And(And(Equal(Image("I"), D(1)), Equal(Image("X"), Named("qubitX"))),
            And(Equal(Image("Y"), Seq(F.Id("i"), Sp, Cdot, Sp, Parenthesized(
                Seq(Named("qubitX"), Sp, Cdot, Sp, Named("qubitZ"))))),
                Equal(Image("Z"), Named("qubitZ")))));
    }

}
