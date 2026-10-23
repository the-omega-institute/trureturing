using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AntidistinguishabilityGramDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/AntidistinguishabilityGram";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/johnstonrussosikora2025antidistinguishability");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional spectral and overlap bounds for antidistinguishability.",
        H("AntidistinguishabilityGram"), Blocks(
            Describe.Lean(DescribeId.Create("isantidistinguishable"),
                DeclarationHandle.Create(Owner + ".IsAntidistinguishable"), H("IsAntidistinguishable"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Section 2.1, page 3: “The set of states is antidistinguishable if there exists a POVM such that ⟨ψi|Mi|ψi⟩ = 0 for all 0 ≤ i ≤ n − 1.” Fin n indexes the measurement effects, and Fin d indexes the finite-dimensional state space."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("csq"),
                DeclarationHandle.Create(Owner + ".cSq"), H("cSq"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Corollary 5.4, page 15: “Let n ≥ 2 be an integer and let S = {|ψ₀⟩, |ψ₁⟩, . . . , |ψₙ₋₁⟩}. If” the displayed source overlap bound holds, “then S is antidistinguishable.” The formula is the square of that source cap, with subtraction and division in ℝ."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("delta"),
                DeclarationHandle.Create(Owner + ".delta"), H("delta"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete definition. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isincoherent"),
                DeclarationHandle.Create(Owner + ".IsIncoherent"), H("IsIncoherent"),
                StatementSource.FromAuthor(Disp(Formula3())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The displayed predicate is the matrix-effect certificate used here: one positive semidefinite summand for each coordinate, with zero on that coordinate’s diagonal. This certificate is consumed by the Gram-to-POVM construction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("locallypsd"),
                DeclarationHandle.Create(Owner + ".LocallyPsd"), H("LocallyPsd"),
                StatementSource.FromAuthor(Disp(Formula4())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The displayed predicate bounds the Hermitian quadratic form on each coordinate hyperplane. It organizes the dual-cone argument."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("orderedspectrum-antitone"),
                DeclarationHandle.Create(Owner + ".orderedSpectrum_antitone"), H("orderedSpectrum antitone"),
                StatementSource.FromAuthor(Disp(Formula5())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("orderedspectrum-nonneg"),
                DeclarationHandle.Create(Owner + ".orderedSpectrum_nonneg"), H("orderedSpectrum nonneg"),
                StatementSource.FromAuthor(Disp(Formula6())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-orderedspectrum"),
                DeclarationHandle.Create(Owner + ".sum_orderedSpectrum"), H("sum orderedSpectrum"),
                StatementSource.FromAuthor(Disp(Formula7())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("grampsd"),
                DeclarationHandle.Create(Owner + ".gramPsd"), H("gramPsd"),
                StatementSource.FromAuthor(Disp(Formula8())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hermitian-projection-complement-psd"),
                DeclarationHandle.Create(Owner + ".hermitian_projection_complement_psd"), H("Positive complementary projection"),
                StatementSource.FromAuthor(Disp(ProjectionComplement())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The complement of a Hermitian idempotent is positive semidefinite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-penrose-exists"),
                DeclarationHandle.Create(Owner + ".matrix_penrose_exists"), H("Matrix Penrose inverse"),
                StatementSource.FromAuthor(Disp(MatrixPenrose())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("Every rectangular complex matrix admits a Penrose inverse: both absorption identities hold and both products are Hermitian. The construction transports the finite-dimensional Moore–Penrose inverse through Matrix.toEuclideanLin."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("psd-summand-kills-kernel"),
                DeclarationHandle.Create(Owner + ".psd_summand_kills_kernel"), H("Kernels of positive summands"),
                StatementSource.FromAuthor(Disp(SummandKernel())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("If a vector belongs to the kernel of a finite sum of positive semidefinite matrices, it belongs to the kernel of every summand."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("psd-summand-projection"),
                DeclarationHandle.Create(Owner + ".psd_summand_projection"), H("Projection of positive summands"),
                StatementSource.FromAuthor(Disp(SummandProjection())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("A Hermitian matrix that fixes the sum of positive semidefinite matrices fixes each summand on both sides."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stategram-diag"),
                DeclarationHandle.Create(Owner + ".stateGram_diag"), H("stateGram diag"),
                StatementSource.FromAuthor(Disp(Formula9())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incoherent-gram-antidistinguishable"),
                DeclarationHandle.Create(Owner + ".incoherent_gram_antidistinguishable"), H("incoherent gram antidistinguishable"),
                StatementSource.FromAuthor(Disp(Formula10())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("A Gram certificate yields positive measurement effects through a finite Penrose inverse and a positive complementary projection. This implication applies to arbitrary finite vector families; normalization is not needed."))), DescribeRole.Theorem))));

    private static Formula Formula0() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(X("n"), Sp, X("d"), Sp, Colon, Sp, Naturals), CloseBrace), Sp,
            Parenthesized(Seq(Psi, Sp, Colon, Sp, X("Fin"), Sp, X("n"), Sp, To, Sp,
                X("EuclideanSpace"), Sp, C, Sp, Parenthesized(FinOf("d")))), Sp, Comma, Sp,
            Eqn(App(X("IsAntidistinguishable"), Psi), Parenthesized(
                Seq(Exists, Sp, Parenthesized(Seq(X("M"), Sp, Colon, Sp,
                    new Formula.TypeArrow(FinOf("n"), Mat("d", "d")))), Sp, Comma, Sp,
                    And(All("i", FinOf("n"), Property(App(X("M"), X("i")), "PosSemidef")),
                        And(Eqn(Parenthesized(Seq(Sum, Sp, X("i"), Sp, Comma, Sp, App(X("M"), X("i")))), D(1)),
                            All("i", FinOf("n"), Eqn(
                                Seq(X("star"), Sp, Parenthesized(Seq(Psi, Sp, X("i"), Sp, Colon, Sp,
                                        FinOf("d"), Sp, To, Sp, C)), Sp, new Formula.Subscript(Cdot, X("v")), Sp,
                                    Parenthesized(Seq(App(X("M"), X("i")), Sp, new Formula.Subscript(Times, X("v")), Sp,
                                        Parenthesized(Seq(Psi, Sp, X("i"), Sp, Colon, Sp, FinOf("d"), Sp, To, Sp, C))))),
                                D(0)))))))));

    private static Formula Formula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("cSq"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(2))), Sp, Slash, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))))));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("delta"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Slash, Sp, Parenthesized(Seq(D(1,6), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(3))))));

    private static Formula Formula3() => All("n", Naturals, All("G", Mat("n", "n"),
        Eqn(App(X("IsIncoherent"), X("G")), Parenthesized(
            Seq(Exists, Sp, Parenthesized(Seq(X("F"), Sp, Colon, Sp,
                new Formula.TypeArrow(FinOf("n"), Mat("n", "n")))), Sp, Comma, Sp,
                And(All("i", FinOf("n"), Property(App(X("F"), X("i")), "PosSemidef")),
                    And(Eqn(Parenthesized(SumF), X("G")),
                        All("i", FinOf("n"), Eqn(App(X("F"), X("i"), X("i"), X("i")), D(0))))))))));

    private static Formula Formula4() => All("n", Naturals, All("Y", Mat("n", "n"),
        Eqn(App(X("LocallyPsd"), X("Y")), Parenthesized(
            And(Property(X("Y"), "IsHermitian"), All("j", FinOf("n"),
                All("x", new Formula.TypeArrow(FinOf("n"), C),
                    Imp(Eqn(App(X("x"), X("j")), D(0)),
                        Seq(D(0), Sp, Leq, Sp, X("RHLinalg"), Sp, Dot, Sp, X("hermForm"), Sp, X("Y"), Sp, X("x"))))))))));

    private static Formula Formula5() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Comma, Sp, F.Id("Antitone"), Sp, Parenthesized(Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k")))))));

    private static Formula Formula6() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("PosSemidef"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, D(0), Sp, Leq, Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("isHermitian"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k"))))), Sp, F.Id("k"));

    private static Formula Formula7() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Sum, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("f"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k"))))), Sp, F.Id("k"))))), Sp, Eq, Sp, Sum, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("j"))));

    private static Formula Formula8() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(F.Id("Matrix"), Sp, Dot, Sp, F.Id("gram"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Psi))), Sp, Dot, Sp, F.Id("PosSemidef"));

    private static Formula Formula9() => All("n", Naturals, All("d", Naturals,
        Seq(Forall, Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, X("Fin"), Sp, X("n"), Sp, To, Sp, X("EuclideanSpace"), Sp, C, Sp, Parenthesized(FinOf("d")))), Sp, Comma, Sp,
            Imp(All("i", FinOf("n"), Eqn(Seq(Vert, Sp, App(Psi, X("i")), Sp, Vert), D(1))),
                All("i", FinOf("n"), Eqn(App(Parenthesized(Seq(X("Matrix"), Sp, Dot, Sp, X("gram"), Sp, C, Sp, Psi)),
                    X("i"), X("i")), D(1)))))));

    private static Formula Formula10() => All("n", Naturals, All("d", Naturals,
        Imp(Seq(D(1), Sp, Leq, Sp, X("n")),
            Seq(Forall, Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, X("Fin"), Sp, X("n"), Sp, To, Sp, X("EuclideanSpace"), Sp, C, Sp, Parenthesized(FinOf("d")))), Sp, Comma, Sp,
                Imp(App(X("IsIncoherent"), Parenthesized(Seq(X("Matrix"), Sp, Dot, Sp, X("gram"), Sp, C, Sp, Psi))),
                    App(X("IsAntidistinguishable"), Psi))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Naturals => Seq(Mathbb, Grp(X("N")));
    private static Formula FinOf(string name) => Seq(X("Fin"), Sp, X(name));
    private static Formula Mat(string rows, string cols) => Seq(X("Matrix"), Sp, Parenthesized(FinOf(rows)), Sp, Parenthesized(FinOf(cols)), Sp, C);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Comma, Sp, body);
    private static Formula Imp(Formula h, Formula body) => Seq(Parenthesized(h), Sp, To, Sp, Parenthesized(body));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Property(Formula a, string name) => Seq(Parenthesized(a), Dot, Operatorname, Grp(X(name)));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula SumF => Seq(Sum, Sp, X("i"), Sp, Colon, Sp, FinOf("n"), Sp, Comma, Sp, App(X("F"), X("i")));
    private static Formula ProjectionComplement() => All("d", Naturals, All("P", Mat("d", "d"),
        Imp(Property(X("P"), "IsHermitian"), Imp(Eqn(Multiply(X("P"), X("P")), X("P")),
            Property(Seq(D(1), Sp, Minus, Sp, X("P")), "PosSemidef")))));
    private static Formula MatrixPenrose() => All("n", Naturals, All("d", Naturals, All("A", Mat("d", "n"),
        Seq(Exists, Sp, Parenthesized(Seq(X("B"), Sp, Colon, Sp, Mat("n", "d"))), Sp, Comma, Sp,
            And(Eqn(Multiply(Multiply(X("A"), X("B")), X("A")), X("A")),
                And(Eqn(Multiply(Multiply(X("B"), X("A")), X("B")), X("B")),
                    And(Property(Multiply(X("A"), X("B")), "IsHermitian"), Property(Multiply(X("B"), X("A")), "IsHermitian"))))))));
    private static Formula SummandKernel() => All("n", Naturals,
        All("F", new Formula.TypeArrow(FinOf("n"), Mat("n", "n")),
            Imp(All("j", FinOf("n"), Property(App(X("F"), X("j")), "PosSemidef")),
                All("x", new Formula.TypeArrow(FinOf("n"), C),
                    Imp(Eqn(MulVector(Parenthesized(SumF), X("x")), D(0)),
                        All("i", FinOf("n"), Eqn(MulVector(App(X("F"), X("i")), X("x")), D(0))))))));
    private static Formula MulVector(Formula a, Formula b) => Seq(a, Sp, new Formula.Subscript(Times, X("v")), Sp, b);
    private static Formula SummandProjection() => All("n", Naturals,
        All("F", new Formula.TypeArrow(FinOf("n"), Mat("n", "n")),
            Imp(All("i", FinOf("n"), Property(App(X("F"), X("i")), "PosSemidef")),
                All("Q", Mat("n", "n"), Imp(Property(X("Q"), "IsHermitian"),
                    Imp(Eqn(Multiply(Parenthesized(SumF), X("Q")), SumF), All("i", FinOf("n"),
                        Eqn(Multiply(Multiply(X("Q"), App(X("F"), X("i"))), X("Q")), App(X("F"), X("i"))))))))));
}
