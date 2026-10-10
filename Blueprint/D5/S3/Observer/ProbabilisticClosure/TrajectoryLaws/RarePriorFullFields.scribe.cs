using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class RarePriorFullFieldsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorFullFields", H("RarePriorFullFields"), Blocks(
            Paragraph(Text("The deterministic acquired row and complete renderer use the original partial native update. Counts and payload-return counters remain in the source. Finite fields retain every write, latch, held record and ordered event block. Factorization holds for every stream, including distinct infinite seed paths.")),
            Node("deterministic-actual-rows", "deterministic_actual_rows", "deterministic actual rows"),
            Node("full-fields-factorization", "full_fields_factorization", "full fields factorization"))));

    private static DocumentBlock.Describe Node(string id, string name, string title) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The statement retains the complete original telescope and conditions."))), DescribeRole.Theorem);

    private static Formula Statement(string name) => name switch
    {
        "deterministic_actual_rows" => Seq(Forall, Sp, Open, Sp, Name("ops"), Sp, Colon, Sp, Name("List"), Sp, Name("Operation"), Sp, Close, Sp, Comma, Sp, Open, Sp, Forall, Sp, Open, Sp, Name("c"), Sp, Colon, Sp, Name("AcquiredNativeState"), Sp, Close, Sp, Comma, Sp, Open, Sp, Open, Sp, Name("run"), Sp, Name("ops"), Sp, Eq, Sp, Name("some"), Sp, Name("c"), Sp, Close, Sp, Rightarrow, Sp, Open, Sp, Exists, Sp, Name("z"), Sp, Colon, Sp, Name("Runtime"), Sp, Comma, Sp, Name("runtimeRun"), Sp, Name("ops"), Sp, Eq, Sp, Name("some"), Sp, Name("z"), Sp, Land, Sp, Name("z"), Sp, Dot, Sp, Name("fields"), Sp, Eq, Sp, Name("c"), Sp, Dot, Sp, Name("source"), Sp, Dot, Sp, Name("finiteFields"), Sp, Land, Sp, Name("NativeObserverJointLaw"), Sp, Dot, Sp, Name("row"), Sp, Name("actualObserver"), Sp, Name("ops"), Sp, Eq, Sp, Name("PMF"), Sp, Dot, Sp, Name("pure"), Sp, Name("z"), Sp, Land, Sp, Open, Sp, Forall, Sp, Name("op"), Sp, Colon, Sp, Name("Operation"), Sp, Comma, Sp, Name("NativeObserverJointLaw"), Sp, Dot, Sp, Name("row"), Sp, Name("actualObserver"), Sp, Open, Sp, Name("ops"), Sp, Plus, Sp, Plus, Sp, OpenBracket, Sp, Name("op"), Sp, CloseBracket, Sp, Close, Sp, Eq, Sp, Name("actualUpdate"), Sp, Name("op"), Sp, Name("z"), Sp, Close, Sp, Close, Sp, Close, Sp, Close),
        "full_fields_factorization" => Seq(Forall, Sp, Open, Sp, Name("c"), Sp, Colon, Sp, Name("AcquiredNativeState"), Sp, Close, Sp, Comma, Sp, Open, Sp, Forall, Sp, Open, Sp, Name("omega"), Sp, Colon, Sp, Name("Stream"), Sp, Close, Sp, Comma, Sp, Open, Sp, Name("fullTranscript"), Sp, Name("c"), Sp, Name("omega"), Sp, Eq, Sp, Name("fieldsTranscript"), Sp, Name("c"), Sp, Dot, Sp, Name("source"), Sp, Dot, Sp, Name("finiteFields"), Sp, Name("omega"), Sp, Land, Sp, Open, Sp, Forall, Sp, Open, Sp, Name("d"), Sp, Colon, Sp, Name("AcquiredNativeState"), Sp, Close, Sp, Comma, Sp, Name("c"), Sp, Dot, Sp, Name("source"), Sp, Dot, Sp, Name("finiteFields"), Sp, Eq, Sp, Name("d"), Sp, Dot, Sp, Name("source"), Sp, Dot, Sp, Name("finiteFields"), Sp, Rightarrow, Sp, Name("fullTranscript"), Sp, Name("c"), Sp, Name("omega"), Sp, Eq, Sp, Name("fullTranscript"), Sp, Name("d"), Sp, Name("omega"), Sp, Close, Sp, Land, Sp, Open, Sp, Forall, Sp, Open, Sp, Name("s"), Sp, Colon, Sp, Name("ActivePhase"), Sp, Close, Sp, Open, Sp, Name("t"), Sp, Colon, Sp, Name("ValidTail"), Sp, Name("s"), Sp, Close, Sp, Comma, Sp, Name("fullRenderer"), Sp, Name("c"), Sp, Name("s"), Sp, Name("t"), Sp, Eq, Sp, Name("fieldsRenderer"), Sp, Name("c"), Sp, Dot, Sp, Name("source"), Sp, Dot, Sp, Name("finiteFields"), Sp, Name("s"), Sp, Name("t"), Sp, Close, Sp, Close, Sp, Close),
        _ => Name("Unknown")
    };
    private static Formula Name(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Seq(params Formula[] items) => F.Seq(items);
}
