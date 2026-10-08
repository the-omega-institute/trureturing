using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.CliffordJointMeasurability;

internal sealed class CentralCycleRealizationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CliffordJointMeasurability/CentralCycleRealizations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized product around the cycle is a central Hermitian involution K.",
        H("Central Cycle Realizations"),
        Blocks(
            Paragraph(Text("Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.")),
            Node("pathword", "pathWord", F0(),
                "The displayed expression defines pathWord.", "pathWord",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("loopsign", "loopSign", F1(),
                "The displayed expression defines loopSign.", "loopSign",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("normalizedloop", "normalizedLoop", F2(),
                "The displayed expression defines normalizedLoop.", "normalizedLoop",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("central-relabel-parent", "central relabel parent", F3(),
                "This central relabel parent identity is used in the CentralCycleRealizations construction.", "central_relabel_parent",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("natural-cycle-adj", "natural cycle adj", F4(),
                "This natural cycle adj identity is used in the CentralCycleRealizations construction.", "natural_cycle_adj",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("cycleprefix", "cyclePrefix", F5(),
                "The displayed expression defines cyclePrefix.", "cyclePrefix",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("realization-cycle-loop", "realization cycle loop", F6(),
                "This realization cycle loop identity is used in the CentralCycleRealizations construction.", "realization_cycle_loop",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("cycle-majorana-extension", "cycle majorana extension", F7(),
                "The normalized product around the cycle is a central Hermitian involution K. It corrects the closing observable before the path extension. The last equation retains K explicitly and verifies the antiperiodic closing bond; no irreducibility or fixed central-sector assumption is imposed.", "cycle_majorana_extension",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Call(owner), Dot, Call(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula F0() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("pathWord"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Call("List"), Sp, Dot, Sp, Call("range"), Sp, F.Id("k"))), Sp, Dot, Sp, Call("map"), Sp, F.Id("A"))), Sp, Dot, Sp, Call("prod"))))
        ]));

    private static Formula F1() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("loopSign"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Eq, Sp, F.Id("n"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(Minus, Sp, D(1)))), F.Id("n"))))
        ]));

    private static Formula F2() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Parenthesized(Seq(Call("normalizedLoop"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Eq, Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Eq, Sp, F.Id("B"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("loopSign"), Sp, F.Id("n"), Sp, Cdot, Sp, Parenthesized(Seq(Call("pathWord"), Sp, F.Id("A"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, F.Id("B"))))))
        ]));

    private static Formula F3() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(new Formula.Subscript(F.Id("v"), D(0)), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("m"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("K"), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(F.Id("K"), Sp, Dot, Sp, Call("IsHermitian"))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("K"), Sp, Cdot, Sp, F.Id("K"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, F.Id("K"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Eq, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Cdot, Sp, F.Id("K"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, F.Id("B"), Sp, F.Id("v"), Sp, Eq, Sp, Call("if"), Sp, F.Id("v"), Sp, Eq, Sp, new Formula.Subscript(F.Id("v"), D(0)), Sp, Call("then"), Sp, F.Id("K"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("v"), Sp, Call("else"), Sp, F.Id("A"), Sp, F.Id("v"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("v"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("B"), Sp, F.Id("v"))), Sp, Dot, Sp, Call("trace"), Sp, Eq, Sp, D(0))), Sp, To),
            Seq(Parenthesized(Seq(Call("JM"), Sp, F.Id("B"), Sp, F.Id("t"))), Sp, To),
            Seq(Call("JM"), Sp, F.Id("A"), Sp, F.Id("t"))
        ]));

    private static Formula F4() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("M"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("cycleGraph"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("Adj"), Sp, F.Id("u"), Sp, F.Id("v"), Sp, Iff, Sp, F.Id("u"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("v"), Sp, Dot, Sp, Call("val"), Sp, Lor, Sp, F.Id("v"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("u"), Sp, Dot, Sp, Call("val"), Sp, Lor, Sp, Parenthesized(Seq(F.Id("u"), Sp, Dot, Sp, Call("val"), Sp, Eq, Sp, D(0), Sp, Land, Sp, F.Id("v"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("M"))), Sp, Lor, Sp, Parenthesized(Seq(F.Id("v"), Sp, Dot, Sp, Call("val"), Sp, Eq, Sp, D(0), Sp, Land, Sp, F.Id("u"), Sp, Dot, Sp, Call("val"), Sp, Plus, Sp, D(1), Sp, Eq, Sp, F.Id("M"))))
        ]));

    private static Formula F5() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("cyclePrefix"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Eq, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Eq, Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, F.Id("k"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, F.Id("M"), Sp, Call("then"), Sp, F.Id("A"), Sp, Seq(Langle, Sp, Seq(F.Id("k"), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, Call("else"), Sp, D(1))))
        ]));

    private static Formula F6() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(2))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("cycleGraph"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, F.Id("A"))), Sp, To),
            Seq(Call("let"), Sp, F.Id("K"), Sp, Colon, Sp, Eq, Sp, Call("normalizedLoop"), Sp, F.Id("n"), Sp, Parenthesized(Seq(Call("cyclePrefix"), Sp, F.Id("A"))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Seq(Langle, Sp, Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle))), Sp, Semi, Sp, F.Id("K"), Sp, Dot, Sp, Call("IsHermitian"), Sp, Land, Sp, F.Id("K"), Sp, Cdot, Sp, F.Id("K"), Sp, Eq, Sp, D(1), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("K"), Sp, Cdot, Sp, F.Id("A"), Sp, F.Id("j"), Sp, Eq, Sp, F.Id("A"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("K"))), Sp, Land, Sp, F.Id("K"), Sp, Cdot, Sp, F.Id("A"), Sp, Seq(Langle, Sp, Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle), Sp, Eq, Sp, Call("loopSign"), Sp, F.Id("n"), Sp, Cdot, Sp, Call("pathWord"), Sp, Parenthesized(Seq(Call("cyclePrefix"), Sp, F.Id("A"))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1))))
        ]));

    private static Formula F7() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(2))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("cycleGraph"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, F.Id("A"))), Sp, To),
            Seq(Call("let"), Sp, F.Id("P"), Sp, Colon, Sp, Eq, Sp, Call("cyclePrefix"), Sp, F.Id("A"), Sp, Semi, Sp, Call("let"), Sp, F.Id("K"), Sp, Colon, Sp, Eq, Sp, Call("normalizedLoop"), Sp, F.Id("n"), Sp, F.Id("P"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Seq(Langle, Sp, Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle))), Sp, Semi, Sp, Call("let"), Sp, F.Id("g"), Sp, Colon, Sp, Eq, Sp, Call("pathMajorana"), Sp, Parenthesized(Seq(Call("liftPath"), Sp, F.Id("P"))), Sp, Parenthesized(Seq(Call("liftSeed"), Sp, F.Id("d"))), Sp, Semi, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, To, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, To, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("k"))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("j"), Sp, Leq, Sp, D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, To, Sp, Forall, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("i"), Sp, Lt, Sp, F.Id("j"), Sp, To, Sp, F.Id("g"), Sp, F.Id("i"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("i"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, To, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))))), Sp, Eq, Sp, Call("liftPath"), Sp, F.Id("P"), Sp, F.Id("k"))), Sp, Land, Sp, Parenthesized(Seq(Minus, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("g"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, F.Id("g"), Sp, D(0))), Sp, Eq, Sp, Parenthesized(Seq(F.Id("K"), Sp, Cdot, Sp, F.Id("A"), Sp, Seq(Langle, Sp, Seq(D(2), Sp, Cdot, Sp, F.Id("n"), Sp, Plus, Sp, D(1), Sp, Comma, Sp, Cdot), Sp, Rangle))), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Call("qubitZ"))
        ]));
}
