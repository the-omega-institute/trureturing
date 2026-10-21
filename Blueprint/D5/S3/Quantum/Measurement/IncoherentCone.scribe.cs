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
            Describe.Lean(DescribeId.Create("psd-closed"),
                DeclarationHandle.Create(Owner + ".psd_closed"), H("psd closed"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, App(X("IsClosed"), Seq(OpenBrace, X("A"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))), Sp, Bar, Sp, Seq(Parenthesized(X("A")), Dot, X("PosSemidef")), CloseBrace))))), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The positive semidefinite matrices form a closed set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flatten-inner"),
                DeclarationHandle.Create(Owner + ".flatten_inner"), H("flatten inner"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("A"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("Z"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(App(X("inner"), Seq(Mathbb, Grp(F.Id("R"))), Parenthesized(App(Qualified("D5", "S3", "Quantum", "Matrix", "CartesianVariance", "vectorize"), X("n"), X("A"))), Parenthesized(App(Qualified("D5", "S3", "Quantum", "Matrix", "CartesianVariance", "vectorize"), X("n"), X("Z")))), Sp, Eq, Sp, App(Qualified("RHLinalg", "rtrace"), Parenthesized(Seq(Seq(Parenthesized(X("A")), Dot, X("conjTranspose")), Sp, Cdot, Sp, X("Z")))))))))), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The real inner product after vectorization equals the real trace pairing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-hermitianpart"),
                DeclarationHandle.Create(Owner + ".trace_hermitianPart"), H("trace hermitianPart"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("G"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(Parenthesized(Seq(Parenthesized(X("G")), Dot, X("IsHermitian"))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("Z"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(App(Qualified("RHLinalg", "rtrace"), Parenthesized(Seq(X("G"), Sp, Cdot, Sp, Parenthesized(Seq(App(X("selfAdjointPart"), Seq(Mathbb, Grp(F.Id("R"))), X("Z")), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C"))))))))), Sp, Eq, Sp, App(Qualified("RHLinalg", "rtrace"), Parenthesized(Seq(X("G"), Sp, Cdot, Sp, X("Z"))))))))))), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The trace pairing with a Hermitian matrix depends only on the self-adjoint part of the other matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rankone-trace"),
                DeclarationHandle.Create(Owner + ".rankone_trace"), H("rankone trace"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("Y"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("x"), Sp, Colon, Sp, Seq(App(X("Fin"), X("n")), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(App(Qualified("RHLinalg", "rtrace"), Parenthesized(Seq(App(Qualified("Matrix", "vecMulVec"), Parenthesized(X("x")), Parenthesized(App(X("star"), Parenthesized(X("x"))))), Sp, Cdot, Sp, X("Y")))), Sp, Eq, Sp, App(Qualified("RHLinalg", "hermForm"), X("Y"), X("x")))))))), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("The trace pairing with an outer product equals the Hermitian quadratic form."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("psd-entry-bound-of-trace"),
                DeclarationHandle.Create(Owner + ".psd_entry_bound_of_trace"), H("psd entry bound of trace"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(X("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("A"), Sp, Colon, Sp, App(X("Matrix"), Parenthesized(App(X("Fin"), X("n"))), Parenthesized(App(X("Fin"), X("n"))), Seq(Mathbb, Grp(F.Id("C")))))), Sp, Comma, Sp, Seq(Parenthesized(Seq(Parenthesized(X("A")), Dot, X("PosSemidef"))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("R"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Comma, Sp, Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, X("R"))), Sp, To, Sp, Seq(Parenthesized(Seq(App(Qualified("RHLinalg", "rtrace"), Parenthesized(X("A"))), Sp, Leq, Sp, X("R"))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("i"), Sp, Colon, Sp, App(X("Fin"), X("n")))), Sp, Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(X("j"), Sp, Colon, Sp, App(X("Fin"), X("n")))), Sp, Comma, Sp, Seq(Seq(Vert, Sp, App(X("A"), X("i"), X("j")), Sp, Vert), Sp, Leq, Sp, X("R")))))))))))), AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text("A positive semidefinite matrix with real trace at most a positive R has every entry of norm at most R."))), DescribeRole.Theorem),
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
    private static Formula X(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(params string[] names) => Seq([.. names.SelectMany((name, index) =>
        index == 0 ? new[] { X(name) } : new[] { Dot, X(name) })]);
    private static Formula App(Formula function, params Formula[] args) =>
        Seq([function, .. args.SelectMany(arg => new[] { Sp, arg })]);
}
