using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class LocallyPositiveSpectrumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/LocallyPositiveSpectrum";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/johnstonrussosikora2025antidistinguishability");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional spectral and overlap bounds for antidistinguishability.",
        H("LocallyPositiveSpectrum"), Blocks(
            Describe.Lean(DescribeId.Create("local-psd-negindex"),
                DeclarationHandle.Create(Owner + ".local_psd_negIndex"), H("local psd negIndex"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-psd-kernel-eq-zero"),
                DeclarationHandle.Create(Owner + ".local_psd_kernel_eq_zero"), H("local psd kernel eq zero"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-psd-reciprocal-budget"),
                DeclarationHandle.Create(Owner + ".local_psd_reciprocal_budget"), H("local psd reciprocal budget"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem))));

    private static Formula Formula0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Parenthesized(Seq(D(1), Sp, Leq, Sp, F.Id("n"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("Y"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("hY"), Sp, Colon, Sp, F.Id("LocallyPsd"), Sp, F.Id("Y"))), Sp, Comma, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("negIndex"), Sp, F.Id("hY"), Sp, Dot, Sp, D(1), Sp, Leq, Sp, D(1));

    private static Formula Formula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("Y"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("LocallyPsd"), Sp, F.Id("Y"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("hermForm"), Sp, F.Id("Y"), Sp, F.Id("v"), Sp, Lt, Sp, D(0))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Y"), Sp, new Formula.Subscript(Times, F.Id("v")), Sp, F.Id("x"), Sp, Eq, Sp, D(0))), Sp, To, Sp, F.Id("x"), Sp, Eq, Sp, D(0));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("Y"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(F.Id("hY"), Sp, Colon, Sp, F.Id("LocallyPsd"), Sp, F.Id("Y"))), Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("hY"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("p"), Sp, Lt, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))), Sp, Comma, Sp, F.Id("i"), Sp, Neq, Sp, F.Id("p"), Sp, To, Sp, D(0), Sp, Lt, Sp, F.Id("hY"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("i"))), Sp, Land, Sp, Parenthesized(Seq(Sum, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("univ"), Sp, Dot, Sp, F.Id("erase"), Sp, F.Id("p"), Sp, Comma, Sp, new Formula.Power(Parenthesized(Seq(F.Id("hY"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("i"))), Seq(Minus, D(1))))), Sp, Leq, Sp, new Formula.Power(Parenthesized(Seq(Minus, Sp, F.Id("hY"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("eigenvalues"), Sp, F.Id("p"))), Seq(Minus, D(1))));
}
