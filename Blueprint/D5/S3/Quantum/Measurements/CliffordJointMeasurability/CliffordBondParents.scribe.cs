using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.CliffordJointMeasurability;

internal sealed class CliffordBondParentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Average the positive Fourier vacuum over Clifford monomials, label each outcome by its bond conjugation signs, and push it to Boolean assignments.",
        H("Clifford Bond Parents"),
        Blocks(
            Paragraph(Text("Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.")),
            Node("cyclecoeff", "cycleCoeff", F0(),
                "The displayed expression defines cycleCoeff.", "cycleCoeff",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("cyclemajoranabond", "cycleMajoranaBond", F1(),
                "The displayed expression defines cycleMajoranaBond.", "cycleMajoranaBond",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("cycle-majorana-parent", "cycle majorana parent", F2(),
                "Average the positive Fourier vacuum over Clifford monomials, label each outcome by its bond conjugation signs, and push it to Boolean assignments. The average normalizes the parent and the Fourier covariance fixes every antiperiodic bond marginal at the threshold.", "cycle_majorana_parent",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("consecutive-majorana-parent", "consecutive majorana parent", F3(),
                "This consecutive majorana parent identity is used in the CliffordBondParents construction.", "consecutive_majorana_parent",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula F0() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))))), Comma),
            Seq(Parenthesized(Seq(Call("cycleCoeff"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Eq, Sp, F.Id("v"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("v"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, D(2), Sp, Cdot, Sp, F.Id("L"), Sp, Call("then"), Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Call("else"), Sp, Minus, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"))))
        ]));

    private static Formula F1() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))))), Comma),
            Seq(Parenthesized(Seq(Call("cycleMajoranaBond"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Iota)), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Eq, Sp, F.Id("v"))), Sp, Colon, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("cycleCoeff"), Sp, F.Id("L"), Sp, F.Id("v"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("g"), Sp, Parenthesized(Seq(Call("finRotate"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, F.Id("v"))))))))
        ]));

    private static Formula F2() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("j"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"))))), Sp, To),
            Seq(Exists, Sp, F.Id("E"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, To, Sp, Call("Bool"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("a"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("E"), Sp, F.Id("a"))), Sp, Dot, Sp, Call("PosSemidef"))), Sp, Land, Sp, Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, Comma, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Sum, Sp, F.Id("a"), Sp, Comma, Sp, Call("outcomeSign"), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("v"))), Sp, Cdot, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, Parenthesized(Seq(Call("visibility"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Call("cycleMajoranaBond"), Sp, F.Id("g"), Sp, F.Id("v"))))
        ]));

    private static Formula F3() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("j"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"))))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("q"), Sp, To, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("q"), Sp, To, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("k"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("val"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("j"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1))), Sp, To),
            Seq(Exists, Sp, F.Id("E"), Sp, Colon, Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("q"), Sp, To, Sp, Call("Bool"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("a"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("E"), Sp, F.Id("a"))), Sp, Dot, Sp, Call("PosSemidef"))), Sp, Land, Sp, Parenthesized(Seq(Sum, Sp, F.Id("a"), Sp, Comma, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Sum, Sp, F.Id("a"), Sp, Comma, Sp, Call("outcomeSign"), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("v"))), Sp, Cdot, Sp, F.Id("E"), Sp, F.Id("a"), Sp, Eq, Sp, Parenthesized(Seq(Call("visibility"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, Parenthesized(Seq(F.Id("j"), Sp, F.Id("v"))), Sp, Cdot, Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("k"), Sp, F.Id("v"))))))))))
        ]));
}
