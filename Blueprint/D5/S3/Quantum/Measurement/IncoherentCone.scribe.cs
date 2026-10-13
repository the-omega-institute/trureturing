using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class IncoherentConeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/IncoherentCone";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/johnstonrussosikora2025antidistinguishability");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional spectral and overlap bounds for antidistinguishability.",
        H("IncoherentCone"), Blocks(
            Describe.Lean(DescribeId.Create("incoherent-closed"),
                DeclarationHandle.Create(Owner + ".incoherent_closed"), H("incoherent closed"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incoherent-separation"),
                DeclarationHandle.Create(Owner + ".incoherent_separation"), H("incoherent separation"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The formula states the complete estimate or implication. Matrix entries, finite index sets, and proof parameters retain their Lean meanings. Proof fields of finite-index constructors are omitted."))), DescribeRole.Theorem))));

    private static Formula Formula1() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("IsClosed"), Sp, Seq(OpenBrace, Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Bar, Sp, F.Id("IsIncoherent"), Sp, F.Id("A")), CloseBrace));

    private static Formula Formula2() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("A"), Sp, Dot, Sp, F.Id("IsHermitian"))), Sp, To, Sp, Parenthesized(Seq(Neg, Sp, F.Id("IsIncoherent"), Sp, F.Id("A"))), Sp, To, Sp, Exists, Sp, F.Id("Y"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Comma, Sp, F.Id("LocallyPsd"), Sp, F.Id("Y"), Sp, Land, Sp, F.Id("RHLinalg"), Sp, Dot, Sp, F.Id("rtrace"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("Y"))), Sp, Lt, Sp, D(0));
}
