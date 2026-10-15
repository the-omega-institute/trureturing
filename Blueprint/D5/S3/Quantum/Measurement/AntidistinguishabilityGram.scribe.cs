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
            Describe.Lean(DescribeId.Create("stategram-diag"),
                DeclarationHandle.Create(Owner + ".stateGram_diag"), H("stateGram diag"),
                StatementSource.FromAuthor(Disp(Formula9())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incoherent-gram-antidistinguishable"),
                DeclarationHandle.Create(Owner + ".incoherent_gram_antidistinguishable"), H("incoherent gram antidistinguishable"),
                StatementSource.FromAuthor(Disp(Formula10())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("A Gram certificate yields positive measurement effects through a finite Penrose inverse and a positive complementary projection. This implication applies to arbitrary finite vector families; normalization is not needed."))), DescribeRole.Theorem))));

    private static Formula Formula0() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, F.Id("IsAntidistinguishable"), Sp, Psi, Sp, Eq, Sp, Exists, Sp, F.Id("M"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("M"), Sp, F.Id("i"))), Sp, Dot, Sp, F.Id("PosSemidef"))), Sp, Land, Sp, Sum, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("M"), Sp, F.Id("i"), Sp, Eq, Sp, D(1), Sp, Land, Sp, Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("star"), Sp, Parenthesized(Seq(Psi, Sp, F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, new Formula.Subscript(Cdot, F.Id("v")), Sp, Parenthesized(Seq(F.Id("M"), Sp, F.Id("i"), Sp, new Formula.Subscript(Times, F.Id("v")), Sp, Parenthesized(Seq(Psi, Sp, F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Eq, Sp, D(0));

    private static Formula Formula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("cSq"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(2))), Sp, Slash, Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))))));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("delta"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(9))), Sp, Slash, Sp, Parenthesized(Seq(D(1,6), Sp, Cdot, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(1))), Sp, Cdot, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Minus, Sp, D(3))))));

    private static Formula Formula3() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("G"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("IsIncoherent"), Sp, F.Id("G"), Sp, Eq, Sp, Exists, Sp, F.Id("F"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("F"), Sp, F.Id("i"))), Sp, Dot, Sp, F.Id("PosSemidef"))), Sp, Land, Sp, Sum, Sp, F.Id("i"), Sp, Comma, Sp, F.Id("F"), Sp, F.Id("i"), Sp, Eq, Sp, F.Id("G"), Sp, Land, Sp, Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("F"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, F.Id("i"), Sp, Eq, Sp, D(0));

    private static Formula Formula4() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("Y"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("LocallyPsd"), Sp, F.Id("Y"), Sp, Eq, Sp, F.Id("Y"), Sp, Dot, Sp, F.Id("IsHermitian"), Sp, Land, Sp, Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, F.Id("x"), Sp, F.Id("j"), Sp, Eq, Sp, D(0), Sp, To, Sp, D(0), Sp, Leq, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("hermForm"), Sp, F.Id("Y"), Sp, F.Id("x"));

    private static Formula Formula5() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Comma, Sp, F.Id("Antitone"), Sp, Parenthesized(Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k")))))));

    private static Formula Formula6() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("PosSemidef"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, D(0), Sp, Leq, Sp, Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("isHermitian"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k"))))), Sp, F.Id("k"));

    private static Formula Formula7() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Sum, Sp, F.Id("k"), Sp, Comma, Sp, F.Id("f"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k"))))), Sp, F.Id("k"))))), Sp, Eq, Sp, Sum, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("hA"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("j"))));

    private static Formula Formula8() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Parenthesized(Seq(F.Id("Matrix"), Sp, Dot, Sp, F.Id("gram"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Psi))), Sp, Dot, Sp, F.Id("PosSemidef"));

    private static Formula Formula9() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Vert, Sp, Psi, Sp, F.Id("i"), Sp, Vert, Sp, Eq, Sp, D(1))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Matrix"), Sp, Dot, Sp, F.Id("gram"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Psi)), Sp, F.Id("i"), Sp, F.Id("i"), Sp, Eq, Sp, D(1));

    private static Formula Formula10() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("IsIncoherent"), Sp, Parenthesized(Parenthesized(Seq(F.Id("Matrix"), Sp, Dot, Sp, F.Id("gram"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Psi))))), Sp, To, Sp, F.Id("IsAntidistinguishable"), Sp, Psi);
}
