using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class HistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-zero auxiliary histories retain all fifteen full calls and their seam configurations.",
        H("Native zero-trigger auxiliary histories"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-reader-no-jumps"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/History.native_reader_no_jumps"),
            H("The stipulated first-zero law forces the constant ready history"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The complete source and extended carriers have cardinalities 89 and 610. The native matrices and their source/tail factorization are those of Global. A source vector chi is arbitrary; the configuration q is required to satisfy chi(q) nonzero. This is the positive-support entrance condition, not an assertion that every source vector can be prepared. Every zero-support coordinate remains in the carrier and in the global vector.")),
                Paragraph(Text("NativeReaderHistory records one finite event list for each of the fifteen actual full forward calls. Each event consists of its internal physical time and the legal tail after the jump. The initial configuration is the unique original ready tail, rather than a chosen new auxiliary initialization. At every call the starting configuration is exactly the preceding call's final configuration. Events at internal time one belong to the ending call and precede report processing. There is no seam resampling or additional seam jump.")),
                Paragraph(Text("auxiliaryCallLaw expresses the stated deterministic zero-trigger rule. Before the next event the current global complex amplitude is nonzero. At the event it is exactly zero, the configuration flips only the actual addressed center along its legal two-point edge, and its new amplitude is nonzero. The recursion then uses that new configuration. An empty remaining event list requires a nonzero current amplitude throughout the remaining closed interval. currentAmplitude uses the full propagated vector without a global projective reset.")),
                Paragraph(Text("The theorem proves existence of one eta, strictly between zero and min(alpha,2*pi-alpha), working for every fixed punctured lambda, every complex source vector and every positive-support q. A native auxiliary history exists, and every history satisfying this exact event law has empty event tables, unchanged ready configuration after fifteen calls, and report b13=false. The proof obtains nonvanishing from the literal native operators, constructs the empty-event history, and rules out a first event in each successive call. Internal times, endpoint events and configuration reuse at seams are retained. The report is taken from the actual final configuration.")),
                Paragraph(Text("This theorem is the conditional auxiliary part of the full instability claim. It does not construct or assume a Bell source probability law, derive the original preparation vector from a finite allowed program, prove ideal correctness at alpha, supply the address-nine probability witness, or prove the full operator12-bound and source/archive continuation. In particular it supplies no probability or total-variation equality, no equality of ideal and actual full joint laws, and no postreport archive which consumes an ideal report. Those remain separate obligations for the complete original statement.")),
                Paragraph(Text("The event-list encoding and standard induction do not earn content. The live mathematical input is the derived source-specific uniform absence of current zeros in the exact full native pulse matrices. Counts, phase identities, conserved quadratic forms, analytic isolation and finite summation are reused or standard bookkeeping. Admission of the new source-specific inference remains subject to the independent expanded proof audit."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Statement() => Disp(Seq(
        Call("card", F.Id("Source")), Sp, Eq, Sp, D(89), Sp, Land, Sp,
        Call("card", F.Id("Extended")), Sp, Eq, Sp, D(610), Sp, Land, Sp,
        Exists, Sp, F.Id("eta"), Colon, Sp, F.Id("Real"), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("eta"), Sp, Land, Sp,
        F.Id("eta"), Sp, Lt, Sp, Call("min", F.Id("alpha"),
            Seq(D(2), Sp, Times, Sp, F.Id("pi"), Sp, Minus, Sp, F.Id("alpha"))), Sp, Land, Sp,
        Forall, Sp, F.Id("lambda"), Colon, Sp, F.Id("Real"), Comma, Sp,
        Call("PuncturedDistanceLess", F.Id("lambda"), F.Id("alpha"), F.Id("eta")), Sp, Implies, Sp,
        Forall, Sp, F.Id("chi"), Colon, Sp, Call("SourceVector"), Comma, Sp,
        Forall, Sp, F.Id("q"), Colon, Sp, F.Id("Source"), Comma, Sp,
        Call("chi", F.Id("q")), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
        Call("Nonempty", Call("NativeReaderHistory", F.Id("chi"), F.Id("q"), F.Id("lambda"))),
        Sp, Land, Sp, Forall, Sp, F.Id("h"), Colon, Sp,
        Call("NativeReaderHistory", F.Id("chi"), F.Id("q"), F.Id("lambda")), Comma, Sp,
        Call("EmptyEventTables", F.Id("h")), Sp, Land, Sp,
        Call("readerConfiguration", Call("events", F.Id("h")), D(15)), Sp, Eq, Sp,
        Call("readyTail", Call("b9", F.Id("q"))), Sp, Land, Sp,
        Call("report", Call("readerConfiguration", Call("events", F.Id("h")), D(15))),
        Sp, Eq, Sp, F.Id("false")));
}
