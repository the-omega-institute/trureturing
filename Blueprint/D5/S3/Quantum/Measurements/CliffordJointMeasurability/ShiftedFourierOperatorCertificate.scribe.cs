using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements.CliffordJointMeasurability;

internal sealed class ShiftedFourierOperatorCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sine-product weights admit a shifted Fourier reduction to a difference of positive weighted Laplacians.",
        H("Shifted Fourier Operator Certificate"),
        Blocks(
            Paragraph(Text("Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.")),
            Node("sine-weights-path-sum", "sine weights path sum", F0(),
                "This sine weights path sum identity is used in the ShiftedFourierOperatorCertificate construction.", "sine_weights_path_sum",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("theta", "theta", F1(),
                "The displayed expression defines theta.", "theta",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("theta-pos", "theta pos", F2(),
                "This theta pos identity is used in the ShiftedFourierOperatorCertificate construction.", "theta_pos",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("theta-mul-l", "theta mul L", F3(),
                "This theta mul L identity is used in the ShiftedFourierOperatorCertificate construction.", "theta_mul_L",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("exponential-sum-orthogonality", "exponential sum orthogonality", F4(),
                "This exponential sum orthogonality identity is used in the ShiftedFourierOperatorCertificate construction.", "exponential_sum_orthogonality",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("phase-star", "phase star", F5(),
                "This phase star identity is used in the ShiftedFourierOperatorCertificate construction.", "phase_star",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("phase-mul", "phase mul", F6(),
                "This phase mul identity is used in the ShiftedFourierOperatorCertificate construction.", "phase_mul",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("phase-cos", "phase cos", F7(),
                "This phase cos identity is used in the ShiftedFourierOperatorCertificate construction.", "phase_cos",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("pathweight", "pathWeight", F8(),
                "The displayed expression defines pathWeight.", "pathWeight",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pathdualweight", "pathDualWeight", F9(),
                "The displayed expression defines pathDualWeight.", "pathDualWeight",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("padcompression", "padCompression", F10(),
                "The displayed expression defines padCompression.", "padCompression",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("padcompression-isometry", "padCompression isometry", F11(),
                "This padCompression isometry identity is used in the ShiftedFourierOperatorCertificate construction.", "padCompression_isometry",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("padcompression-compress", "padCompression compress", F12(),
                "This padCompression compress identity is used in the ShiftedFourierOperatorCertificate construction.", "padCompression_compress",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("pathweight-sine", "pathWeight sine", F13(),
                "This pathWeight sine identity is used in the ShiftedFourierOperatorCertificate construction.", "pathWeight_sine",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("path-dual-operator-certificate", "path dual operator certificate", F14(),
                "The sine-product weights admit a shifted Fourier reduction to a difference of positive weighted Laplacians. Its positive trace is cot(theta (n+1)). The Majorana quadratic bound and the ancilla compression give this operator inequality for every path realization and every Boolean outcome.", "path_dual_operator_certificate",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("visibility-as-l", "visibility as L", F15(),
                "This visibility as L identity is used in the ShiftedFourierOperatorCertificate construction.", "visibility_as_L",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("visibility-icc", "visibility Icc", F16(),
                "This visibility Icc identity is used in the ShiftedFourierOperatorCertificate construction.", "visibility_Icc",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("visibility-upper-of-weighted", "visibility upper of weighted", F17(),
                "This visibility upper of weighted identity is used in the ShiftedFourierOperatorCertificate construction.", "visibility_upper_of_weighted",
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
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("K"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Call("let"), Sp, Theta, Sp, Colon, Sp, Eq, Sp, Call("Real"), Sp, Dot, Sp, Call("pi"), Sp, Slash, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("K"), Sp, Plus, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Semi, Sp, Parenthesized(Seq(Sum, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Finset"), Sp, Dot, Sp, Call("range"), Sp, F.Id("K"), Sp, Comma, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, Theta)), Sp, Cdot, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(2))), Sp, Cdot, Sp, Theta)))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("K"), Sp, Plus, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Slash, Sp, D(2), Sp, Cdot, Sp, Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, Theta)
        ]));

    private static Formula F1() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("pi"), Sp, Slash, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))))))))
        ]));

    private static Formula F2() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("L"))), Sp, To),
            Seq(D(0), Sp, Lt, Sp, Call("theta"), Sp, F.Id("L"))
        ]));

    private static Formula F3() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("L"))), Sp, To),
            Seq(Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Call("theta"), Sp, F.Id("L"), Sp, Eq, Sp, Call("Real"), Sp, Dot, Sp, Call("pi"), Sp, Slash, Sp, D(2))
        ]));

    private static Formula F4() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("M"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("M"))), Comma),
            Seq(Parenthesized(Seq(Sum, Sp, F.Id("j"), Sp, InMacro, Sp, Call("Finset"), Sp, Dot, Sp, Call("range"), Sp, F.Id("M"), Sp, Comma, Sp, Call("Complex"), Sp, Dot, Sp, Call("exp"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(D(2), Sp, Cdot, Sp, Call("Real"), Sp, Dot, Sp, Call("pi"), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))))), Sp, Slash, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))))), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Call("Complex"), Sp, Dot, Sp, F.Id("I"))))), Sp, Eq, Sp, Call("if"), Sp, F.Id("r"), Sp, Eq, Sp, F.Id("s"), Sp, Call("then"), Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Call("else"), Sp, D(0))
        ]));

    private static Formula F5() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Call("star"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, F.Id("x"))), Sp, Eq, Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(Minus, Sp, F.Id("x"))))
        ]));

    private static Formula F6() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("y"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, F.Id("x"), Sp, Cdot, Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, F.Id("y"), Sp, Eq, Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(F.Id("x"), Sp, Plus, Sp, F.Id("y"))))
        ]));

    private static Formula F7() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, F.Id("x"), Sp, Plus, Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Mapsto, Sp, Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("probChar"), Sp, F.Id("x"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Parenthesized(Seq(Minus, Sp, F.Id("x"))))), Sp, Slash, Sp, D(2))
        ]));

    private static Formula F8() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(Call("pathWeight"), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Eq, Sp, F.Id("L"))), Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Eq, Sp, F.Id("j"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, Parenthesized(Seq(Call("theta"), Sp, F.Id("L"))), Sp, Minus, Sp, Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, Parenthesized(Seq(Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("j"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, Call("theta"), Sp, F.Id("L"))))), Sp, Slash, Sp, D(2))))
        ]));

    private static Formula F9() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Comma),
            Seq(Parenthesized(Seq(Call("pathDualWeight"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Eq, Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Eq, Sp, F.Id("k"))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Eq, Sp, Parenthesized(Seq(Call("pathWeight"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Plus, Sp, D(1))))))
        ]));

    private static Formula F10() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("padCompression"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Eq, Sp, F.Id("d"))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Call("Fin"), Sp, F.Id("d"))))), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))))
        ]));

    private static Formula F11() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(Call("padCompression"), Sp, F.Id("d"))), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, Call("padCompression"), Sp, F.Id("d"), Sp, Eq, Sp, D(1))
        ]));

    private static Formula F12() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"), Sp, Times, Sp, Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("padCompression"), Sp, F.Id("d"))), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("B"), Sp, Parenthesized(Qualified("Matrix", "kronecker")), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))), Sp, Parenthesized(Seq(Call("Fin"), Sp, D(2))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Cdot, Sp, Call("padCompression"), Sp, F.Id("d"), Sp, Eq, Sp, Parenthesized(Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Call("Fin"), Sp, F.Id("d")))))), Sp, Dot, Sp, Call("conjTranspose"), Sp, Cdot, Sp, F.Id("B"), Sp, Cdot, Sp, Parenthesized(Seq(Call("qubitV"), Sp, Parenthesized(Seq(Iota, Sp, Colon, Sp, Eq, Sp, Call("Fin"), Sp, F.Id("d"))))))
        ]));

    private static Formula F13() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Call("pathWeight"), Sp, F.Id("L"), Sp, F.Id("j"), Sp, Eq, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(F.Id("j"), Sp, Cdot, Sp, Call("theta"), Sp, F.Id("L"))), Sp, Cdot, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("j"), Sp, Plus, Sp, D(1))), Sp, Cdot, Sp, Call("theta"), Sp, F.Id("L"))))
        ]));

    private static Formula F14() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Comma),
            Seq(Parenthesized(Seq(Call("Realization"), Sp, Parenthesized(Seq(Call("SimpleGraph"), Sp, Dot, Sp, Call("pathGraph"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Sp, F.Id("A"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))), Sp, To, Sp, Call("Bool"))), Comma),
            Seq(Parenthesized(Seq(Parenthesized(Parenthesized(Seq(Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Slash, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Parenthesized(Seq(Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Minus, Sp, Call("weightedHamiltonian"), Sp, F.Id("A"), Sp, Parenthesized(Seq(Call("pathDualWeight"), Sp, F.Id("n"))), Sp, F.Id("a"))), Sp, Dot, Sp, Call("PosSemidef"))
        ]));

    private static Formula F15() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Call("visibility"), Sp, F.Id("n"), Sp, Eq, Sp, D(1), Sp, Slash, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))))))
        ]));

    private static Formula F16() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Call("visibility"), Sp, F.Id("n"), Sp, InMacro, Sp, Call("Set"), Sp, Dot, Sp, Call("Icc"), Sp, Parenthesized(Seq(D(0), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, D(1))
        ]));

    private static Formula F17() => Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma),
            Seq(Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To),
            Seq(Forall, Sp, Parenthesized(Seq(F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Comma),
            Seq(Parenthesized(Seq(F.Id("t"), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))))), Sp, Leq, Sp, Call("Real"), Sp, Dot, Sp, Call("cos"), Sp, Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Slash, Sp, Call("Real"), Sp, Dot, Sp, Call("sin"), Sp, Parenthesized(Seq(Call("theta"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))))), Sp, To),
            Seq(F.Id("t"), Sp, Leq, Sp, Call("visibility"), Sp, F.Id("n"))
        ]));
}
