using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.CliffordJointMeasurability;

internal sealed class FourierCliffordVacuumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product of Fourier number projections is a Hermitian idempotent.",
        H("Fourier Clifford Vacuum"),
        Blocks(
            Paragraph(Text("Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.")),
            Node("averaging", "averaging", F0(),
                "The displayed expression defines averaging.", "averaging",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("finitetwirl", "finiteTwirl", F1(),
                "The displayed expression defines finiteTwirl.", "finiteTwirl",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("finitetwirl-step", "finiteTwirl step", F2(),
                "This finiteTwirl step identity is used in the FourierCliffordVacuum construction.", "finiteTwirl_step",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("vacuumword", "vacuumWord", F3(),
                "The displayed expression defines vacuumWord.", "vacuumWord",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("cyclefrequency", "cycleFrequency", F5(),
                "The displayed expression defines cycleFrequency.", "cycleFrequency",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("modescale", "modeScale", F6(),
                "The displayed expression defines modeScale.", "modeScale",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("modecoeff", "modeCoeff", F7(),
                "The displayed expression defines modeCoeff.", "modeCoeff",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("modescale-star", "modeScale star", F8(),
                "This modeScale star identity is used in the FourierCliffordVacuum construction.", "modeScale_star",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("modescale-square", "modeScale square", F9(),
                "This modeScale square identity is used in the FourierCliffordVacuum construction.", "modeScale_square",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("fouriermode", "fourierMode", F10(),
                "The displayed expression defines fourierMode.", "fourierMode",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("totalgamma", "totalGamma", F11(),
                "The displayed expression defines totalGamma.", "totalGamma",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("cliffordaverage", "cliffordAverage", F12(),
                "The displayed expression defines cliffordAverage.", "cliffordAverage",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("totalmode", "totalMode", F13(),
                "The displayed expression defines totalMode.", "totalMode",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("numberprojection", "numberProjection", F14(),
                "The displayed expression defines numberProjection.", "numberProjection",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fouriervacuum", "fourierVacuum", F15(),
                "The displayed expression defines fourierVacuum.", "fourierVacuum",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("fouriervacuum-properties", "fourierVacuum properties", F16(),
                "The product of Fourier number projections is a Hermitian idempotent. Every Fourier annihilator kills it on the left and its adjoint kills it on the right. Averaging conjugations by all Majoranas gives exactly 2^(−L) times the identity.", "fourierVacuum_properties",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("fouriervacuum-psd", "fourierVacuum psd", F17(),
                "This fourierVacuum psd identity is used in the FourierCliffordVacuum construction.", "fourierVacuum_psd",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("fouriervacuum-covariance", "fourierVacuum covariance", F18(),
                "This fourierVacuum covariance identity is used in the FourierCliffordVacuum construction.", "fourierVacuum_covariance",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula F0() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Parenthesized(Seq(Call("averaging"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("u"), Sp, Colon, Sp, Eq, Sp, F.Id("u"))), Sp, Colon, Sp, F.Id("R"), Sp, Seq(To, Underscore, Grp(F.Id("l"))), Sp, Seq(OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(Call("LinearMap"), Sp, Dot, Sp, Call("id"), Sp, Plus, Sp, Parenthesized(Seq(Call("LinearMap"), Sp, Dot, Sp, Call("mulLeftRight"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("u"), Sp, Comma, Sp, F.Id("u"))))))))))
        ]));

    private static Formula F1() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("finiteTwirl"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, F.Id("R"), Sp, Seq(To, Underscore, Grp(F.Id("l"))), Sp, Seq(OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Call("List"), Sp, Dot, Sp, Call("range"), Sp, F.Id("k"))), Sp, Dot, Sp, Call("map"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("j"), Sp, Mapsto, Sp, Call("averaging"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))))))), Sp, Dot, Sp, Call("prod"))))
        ]));

    private static Formula F2() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("X"), Sp, Colon, Sp, F.Id("R"))), Comma),
            Seq(Call("finiteTwirl"), Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Plus, Sp, D(1))), Sp, F.Id("X"), Sp, Eq, Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(Call("finiteTwirl"), Sp, F.Id("g"), Sp, F.Id("k"), Sp, F.Id("X"), Sp, Plus, Sp, Call("finiteTwirl"), Sp, F.Id("g"), Sp, F.Id("k"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("X"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"))))))
        ]));

    private static Formula F3() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("vacuumWord"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Eq, Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Call("List"), Sp, Dot, Sp, Call("range"), Sp, F.Id("k"))), Sp, Dot, Sp, Call("reverse"))), Sp, Dot, Sp, Call("map"), Sp, F.Id("p"))), Sp, Dot, Sp, Call("prod"))))
        ]));

    private static Formula F5() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("L"))), Comma),
            Seq(Parenthesized(Seq(Call("cycleFrequency"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Eq, Sp, F.Id("r"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, Call("theta"), Sp, F.Id("L"))))
        ]));

    private static Formula F6() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("modeScale"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Parenthesized(Seq(Parenthesized(Seq(new Formula.Power(Parenthesized(Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("sqrt"), Sp, Parenthesized(Seq(Parenthesized(Seq(D(4), Sp, Cdot, Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))))))), Seq(Minus, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))))
        ]));

    private static Formula F7() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("L"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))))), Comma),
            Seq(Parenthesized(Seq(Call("modeCoeff"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Eq, Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Eq, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("modeScale"), Sp, F.Id("L"), Sp, Cdot, Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(Minus, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Call("cycleFrequency"), Sp, F.Id("L"), Sp, F.Id("r"))))))
        ]));

    private static Formula F8() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Call("star"), Sp, Parenthesized(Seq(Call("modeScale"), Sp, F.Id("L"))), Sp, Eq, Sp, Call("modeScale"), Sp, F.Id("L"))
        ]));

    private static Formula F9() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("L"))), Sp, To),
            Seq(Call("modeScale"), Sp, F.Id("L"), Sp, Cdot, Sp, Call("modeScale"), Sp, F.Id("L"), Sp, Eq, Sp, new Formula.Power(Parenthesized(Parenthesized(Seq(Parenthesized(Seq(D(4), Sp, Cdot, Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))), Seq(Minus, D(1))))
        ]));

    private static Formula F10() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("L"))), Comma),
            Seq(Parenthesized(Seq(Call("fourierMode"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Eq, Sp, F.Id("r"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("Fintype"), Sp, Dot, Sp, Call("linearCombination"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("g"), Sp, Parenthesized(Seq(Call("modeCoeff"), Sp, F.Id("L"), Sp, F.Id("r"))))))
        ]));

    private static Formula F11() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("totalGamma"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, Call("hk"), Sp, Colon, Sp, F.Id("k"), Sp, Lt, Sp, D(2), Sp, Cdot, Sp, F.Id("L"), Sp, Call("then"), Sp, F.Id("g"), Sp, Seq(Langle, Sp, Seq(F.Id("k"), Sp, Comma, Sp, Call("hk")), Sp, Rangle), Sp, Call("else"), Sp, D(0))))
        ]));

    private static Formula F12() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Parenthesized(Seq(Call("cliffordAverage"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Colon, Sp, F.Id("R"), Sp, Seq(To, Underscore, Grp(F.Id("l"))), Sp, Seq(OpenBracket, Seq(Mathbb, Grp(F.Id("C"))), CloseBracket), Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("finiteTwirl"), Sp, Parenthesized(Seq(Call("totalGamma"), Sp, F.Id("g"))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))))))
        ]));

    private static Formula F13() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("totalMode"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("if"), Sp, Call("hk"), Sp, Colon, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("L"), Sp, Call("then"), Sp, Call("fourierMode"), Sp, F.Id("g"), Sp, Seq(Langle, Sp, Seq(F.Id("k"), Sp, Comma, Sp, Call("hk")), Sp, Rangle), Sp, Call("else"), Sp, D(0))))
        ]));

    private static Formula F14() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("StarRing"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("numberProjection"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("totalMode"), Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, Call("star"), Sp, Parenthesized(Seq(Call("totalMode"), Sp, F.Id("g"), Sp, F.Id("k"))))))
        ]));

    private static Formula F15() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("StarRing"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Parenthesized(Seq(Call("fourierVacuum"), Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Eq, Sp, F.Id("R"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Eq, Sp, F.Id("g"))), Sp, Colon, Sp, F.Id("R"))), Sp, Eq, Sp, Parenthesized(Seq(Call("vacuumWord"), Sp, Parenthesized(Seq(Call("numberProjection"), Sp, F.Id("g"))), Sp, F.Id("L"))))
        ]));

    private static Formula F16() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("StarRing"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("StarModule"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("L"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("j"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"))))), Sp, To),
            Seq(Call("star"), Sp, Parenthesized(Seq(Call("fourierVacuum"), Sp, F.Id("g"))), Sp, Eq, Sp, Call("fourierVacuum"), Sp, F.Id("g"), Sp, Land, Sp, Call("fourierVacuum"), Sp, F.Id("g"), Sp, Cdot, Sp, Call("fourierVacuum"), Sp, F.Id("g"), Sp, Eq, Sp, Call("fourierVacuum"), Sp, F.Id("g"), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("k"), Sp, Lt, Sp, F.Id("L"), Sp, To, Sp, Call("totalMode"), Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, Call("fourierVacuum"), Sp, F.Id("g"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Call("fourierVacuum"), Sp, F.Id("g"), Sp, Cdot, Sp, Call("star"), Sp, Parenthesized(Seq(Call("totalMode"), Sp, F.Id("g"), Sp, F.Id("k"))), Sp, Eq, Sp, D(0))), Sp, Land, Sp, Call("cliffordAverage"), Sp, F.Id("g"), Sp, Parenthesized(Seq(Call("fourierVacuum"), Sp, F.Id("g"))), Sp, Eq, Sp, Parenthesized(new Formula.Power(Parenthesized(Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))), F.Id("L"))), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, F.Id("R"))))
        ]));

    private static Formula F17() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Fintype"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("DecidableEq"), Sp, Iota), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("L"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, Call("Matrix"), Sp, Iota, Sp, Iota, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("j"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"))))), Sp, To),
            Seq(Parenthesized(Seq(Call("fourierVacuum"), Sp, F.Id("g"))), Sp, Dot, Sp, Call("PosSemidef"))
        ]));

    private static Formula F18() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("R"), Sp, Colon, Sp, Call("Type"))), Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Ring"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("Algebra"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("StarRing"), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Grp(), OpenBracket, Seq(Call("StarModule"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, F.Id("R")), CloseBracket, Sp, Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("L"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("g"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))), Sp, To, Sp, F.Id("R"))), Comma),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Eq, Sp, D(1))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"))), Sp, Eq, Sp, F.Id("g"), Sp, F.Id("j"))), Sp, To),
            Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, F.Id("k"), Sp, Comma, Sp, F.Id("j"), Sp, Neq, Sp, F.Id("k"), Sp, To, Sp, F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Eq, Sp, Minus, Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("j"))))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("L"))))), Comma),
            Seq(Call("cliffordAverage"), Sp, F.Id("g"), Sp, Parenthesized(Seq(F.Id("g"), Sp, F.Id("j"), Sp, Cdot, Sp, F.Id("g"), Sp, F.Id("k"), Sp, Cdot, Sp, Call("fourierVacuum"), Sp, F.Id("g"))), Sp, Eq, Sp, Parenthesized(Seq(D(4), Sp, Cdot, Sp, Sum, Sp, F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("L"), Sp, Comma, Sp, Call("star"), Sp, Parenthesized(Seq(Call("modeCoeff"), Sp, F.Id("L"), Sp, F.Id("r"), Sp, F.Id("j"))), Sp, Cdot, Sp, Call("modeCoeff"), Sp, F.Id("L"), Sp, F.Id("r"), Sp, F.Id("k"))), Sp, Cdot, Sp, Call("cliffordAverage"), Sp, F.Id("g"), Sp, Parenthesized(Seq(Call("fourierVacuum"), Sp, F.Id("g"))))
        ]));
}
