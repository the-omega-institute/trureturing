using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AntidistinguishabilitySpectrumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/johnstonrussosikora2025antidistinguishability");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional spectral and overlap bounds for antidistinguishability.",
        H("AntidistinguishabilitySpectrum"), Blocks(
            Describe.Lean(DescribeId.Create("spectralbalanced"),
                DeclarationHandle.Create(Owner + ".SpectralBalanced"), H("SpectralBalanced"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The displayed predicate compares every eigenvalue square root against the sum over its complement. It organizes the spectral pairing proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spectral-balanced-pairing-nonneg"),
                DeclarationHandle.Create(Owner + ".spectral_balanced_pairing_nonneg"), H("spectral balanced pairing nonneg"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-sufficient-antidistinguishable"),
                DeclarationHandle.Create(Owner + ".spectral_sufficient_antidistinguishable"), H("spectral sufficient antidistinguishable"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("Theorem 5.1, page 12: “Let n ≥ 2 be an integer and let G ∈ Pos(ℂⁿ) be the Gram matrix of a set S of n pure states, and let λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ₋₁ be the eigenvalues of G.” Its displayed square-root inequality implies antidistinguishability. The ordered values are read through the canonical finite eigenvalue equivalence. The displayed Lean implication also applies to unnormalized vectors; normalization is not used in this implication."))), DescribeRole.Theorem))));

    private static Formula Formula0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Seq(OpenBrace, Seq(F.Id("G"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, F.Id("G"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, Comma, Sp, F.Id("SpectralBalanced"), Sp, F.Id("hG"), Sp, Eq, Sp, Forall, Sp, Parenthesized(Seq(F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("Real"), Sp, Dot, Sp, F.Id("sqrt"), Sp, Parenthesized(Seq(F.Id("hG"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("j"))), Sp, Leq, Sp, Sum, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("univ"), Sp, Dot, Sp, F.Id("erase"), Sp, F.Id("j"), Sp, Comma, Sp, F.Id("Real"), Sp, Dot, Sp, F.Id("sqrt"), Sp, Parenthesized(Seq(F.Id("hG"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("i"))));

    private static Formula Formula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("G"), Sp, F.Id("Y"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("hG"), Sp, Colon, Sp, F.Id("G"), Sp, Dot, Sp, F.Id("PosSemidef"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("SpectralBalanced"), Sp, F.Id("hG"), Sp, Dot, Sp, F.Id("isHermitian"))), Sp, To, Sp, Parenthesized(Seq(F.Id("LocallyPsd"), Sp, F.Id("Y"))), Sp, To, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("rtrace"), Sp, Parenthesized(Seq(F.Id("G"), Sp, Cdot, Sp, F.Id("Y"))), Sp, Geq, Sp, D(0));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Psi, Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("EuclideanSpace"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Real"), Sp, Dot, Sp, F.Id("sqrt"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("gramPsd"), Sp, Psi)), Sp, Dot, Sp, F.Id("isHermitian"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k"))))), Sp, Seq(Langle, Sp, D(0), Rangle))), Sp, Leq, Sp, Sum, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("univ"), Sp, Dot, Sp, F.Id("erase"), Sp, Parenthesized(Seq(Seq(Langle, Sp, D(0), Rangle), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("Real"), Sp, Dot, Sp, F.Id("sqrt"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("fun"), Sp, F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("gramPsd"), Sp, Psi)), Sp, Dot, Sp, F.Id("isHermitian"), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("finCongr"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Eq, Sp, F.Id("Fintype"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("eigEquiv"))), Sp, F.Id("k"))))), Sp, F.Id("i"))))), Sp, To, Sp, F.Id("IsAntidistinguishable"), Sp, Psi);
}
