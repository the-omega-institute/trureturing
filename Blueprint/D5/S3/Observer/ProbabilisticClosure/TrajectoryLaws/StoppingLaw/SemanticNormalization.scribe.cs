using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw;

internal sealed class SemanticNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact normalization of capped semantic read rules", H("Exact normalization of capped semantic read rules"), Blocks(
            Paragraph(Text("A source is a phase phi and a two-sided Boolean spin sequence S. At the active integer address 2e+phi, the visible reply is the XOR of S(e) and S(e+1); separator replies are zero. The hidden value uses the original integer endpoint, including the negative seam. RawRule.next depends only on the unchanged seed and the ordered acquired record. Finite nonnegative waits are separate from a terminal nonreturn.")),
            Paragraph(Text("ReadTree has integer-labelled binary read nodes and leaves labelled by an optional hidden output. Execution retains the complete ordered address/reply record. paid is its length, so repeated and separator calls remain charged. A none leaf records nonreturn at its exact depth. TotalCap bounds the uncapped extended-natural paidCount on every phase, spin sequence and seed, including exceptional paths.")),
            Describe.Lean(DescribeId.Create("unfold-correct"), DeclarationHandle.Create(Prefix + "unfold_correct"),
                H("Exact suffix execution"), StatementSource.FromAuthor(Disp(All("U", N("Type"), WithMeasurable(N("U"), All("Q", A("RawRule", N("U")), All("u", N("U"), All("x", Arrow(N("Int"), N("Bool")), All("k", N("Nat"), All("n", N("Nat"), All("r", N("Record"), Imp(Conj(Equal(A("readPrefix", N("Q"), N("u"), N("x"), N("n")), A("some", N("r"))), All("m", N("Nat"), All("s", N("Record"), Imp(Equal(A("readPrefix", N("Q"), N("u"), N("x"), N("m")), A("some", N("s"))), Leq(N("m"), PlusOf(N("n"), N("k"))))))), Let("v", A("run", A("unfold", N("Q"), N("k"), N("u"), N("r")), N("x")), Conj(Equal(A("readPrefix", N("Q"), N("u"), N("x"), PlusOf(N("n"), A("paid", N("v")))), A("some", A("append", N("r"), A("record", N("v"))))), Equal(A("next", N("Q"), N("u"), A("append", N("r"), A("record", N("v")))), A("terminal", A("output", N("v"))))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Starting at any acquired record with at most k further calls, unfolding reaches the original terminal event with precisely the appended execution record. The induction is on the remaining call budget; a further read at budget zero contradicts the cap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalization-pointwise"), DeclarationHandle.Create(Prefix + "normalization_pointwise"),
                H("Pointwise preservation on every actual capped path"), StatementSource.FromAuthor(Disp(All("U", N("Type"), WithMeasurable(N("U"), All("Q", A("RawRule", N("U")), All("k", N("Nat"), Imp(A("TotalCap", N("Q"), N("k")), All("phi", N("Bool"), All("S", N("Spins"), All("u", N("U"), Conj(A("Completes", N("Q"), N("u"), A("visible", N("phi"), N("S")), A("run", A("normalize", N("Q"), N("k"), N("u")), A("visible", N("phi"), N("S")))), Equal(A("output", N("Q"), N("u"), A("visible", N("phi"), N("S"))), A("output", A("run", A("normalize", N("Q"), N("k"), N("u")), A("visible", N("phi"), N("S"))))), Equal(A("paidCount", N("Q"), N("u"), A("visible", N("phi"), N("S"))), A("paid", A("run", A("normalize", N("Q"), N("k"), N("u")), A("visible", N("phi"), N("S")))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("normalize unfolds from the empty record. Completes identifies its exact original terminal record, output and paid count. Return/nonreturn indicators agree as well: a finite number of finite waits remains finite. The height bound applies to every formal branch, with no padding of earlier terminals."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurable-normalize"), DeclarationHandle.Create(Prefix + "measurable_normalize"),
                H("Measurable ordinary tree selector"), StatementSource.FromAuthor(Disp(All("U", N("Type"), WithMeasurable(N("U"), All("Q", A("RawRule", N("U")), All("k", N("Nat"), Imp(A("Lawful", N("Q")), A("Measurable", A("normalize", N("Q"), N("k")))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite tree type is countable and carries its discrete measurable structure. Measurability follows by induction through next-event decisions at countably many records."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("completion-normalization-bridge"), DeclarationHandle.Create(Prefix + "completion_normalization_bridge"),
                H("One common ordinary version for seed completion"), StatementSource.FromAuthor(Disp(All("U", N("Type"), WithMeasurable(N("U"), All("Q", A("RawRule", N("U")), All("nu", A("Measure", N("U")), All("k", N("Nat"), Imp(Conj(A("CompletionLawful", N("Q"), N("nu")), A("TotalCap", N("Q"), N("k"))), Some("T", Arrow(N("U"), A("CappedTrees", N("k"))), Conj(A("Measurable", N("T")), Ae("u", N("nu"), Equal(A("normalize", N("Q"), N("k"), N("u")), A("val", A("apply", N("T"), N("u"))))), Ae("u", N("nu"), All("phi", N("Bool"), All("S", N("Spins"), Conj(A("Completes", N("Q"), N("u"), A("visible", N("phi"), N("S")), A("run", A("val", A("apply", N("T"), N("u"))), A("visible", N("phi"), N("S")))), Equal(A("output", N("Q"), N("u"), A("visible", N("phi"), N("S"))), A("output", A("run", A("val", A("apply", N("T"), N("u"))), A("visible", N("phi"), N("S"))))), Equal(A("paidCount", N("Q"), N("u"), A("visible", N("phi"), N("S"))), A("paid", A("run", A("val", A("apply", N("T"), N("u"))), A("visible", N("phi"), N("S"))))))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CappedTrees(k) is the subtype of trees of height at most k. One measurable selector agrees for almost every seed; on that common set it preserves every source execution. This statement does not assert pointwise agreement of arbitrary completed versions at every seed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalize-realize"), DeclarationHandle.Create(Prefix + "normalize_realize"),
                H("Exact recovery of a bounded tree family"), StatementSource.FromAuthor(Disp(All("U", N("Type"), WithMeasurable(N("U"), All("T", Arrow(N("U"), N("ReadTree")), All("k", N("Nat"), All("u", N("U"), Imp(Leq(A("height", A("apply", N("T"), N("u"))), N("k")), Equal(A("normalize", A("realize", N("T")), N("k"), N("u")), A("apply", N("T"), N("u"))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("realize follows the ordered acquired record, rejecting inconsistent addresses. When the supplied tree already has height at most k, normalization recovers it exactly."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalization-version"), DeclarationHandle.Create(Prefix + "normalization_version"),
                H("Ordinary selector for ambient completed events"), StatementSource.FromAuthor(Disp(All("U", N("Type"), WithMeasurable(N("U"), All("Q", A("CompletedRule", N("U")), All("mu", A("Measure", A("Prod", N("SourcePoint"), N("U"))), All("k", N("Nat"), Imp(A("Lawful", N("Q"), N("mu")), Some("T", Arrow(N("U"), A("CappedTrees", N("k"))), Conj(A("Measurable", N("T")), Ae("p", N("mu"), Equal(A("normalize", N("Q"), N("k"), N("p")), A("val", A("apply", N("T"), A("snd", N("p")))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CompletedRule allows source-dependent ambient-null versions of the available observation field. A single ordinary seed selector agrees product-almost everywhere. Separately, completed_normalization_execution preserves each actual completed execution under its all-path cap; that pointwise execution assertion is distinct from the almost-everywhere selector identity."))), DescribeRole.Theorem),
            Paragraph(Text("The normalization construction changes neither the seed space nor the actual read clock. It is a finite semantic unfolding and does not decide divergence of arbitrary programs.")))));
    private static Formula N(string name) => F.Seq(Operatorname, Grp(F.Id(name)));
    private static Formula A(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.Add(F.Seq(Comma, Sp));
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return F.Seq(parts.ToArray());
    }
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(Forall, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula Some(string name, Formula type, Formula body) =>
        F.Seq(Exists, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Comma, Sp, Open, body, Close);
    private static Formula Ae(string name, Formula measure, Formula body) =>
        A("AE", measure, F.Seq(N("fun"), Sp, N(name), Sp, Mapsto, Sp, Open, body, Close));
    private static Formula Equal(Formula x, Formula y) => F.Seq(x, Sp, Eq, Sp, y);
    private static Formula Leq(Formula x, Formula y) => F.Seq(x, Sp, Le, Sp, y);
    private static Formula Imp(Formula x, Formula y) => F.Seq(Open, x, Close, Sp, To, Sp, Open, y, Close);
    private static Formula Arrow(Formula x, Formula y) => F.Seq(Open, x, Sp, To, Sp, y, Close);
    private static Formula PlusOf(Formula x, Formula y) => F.Seq(Open, x, Sp, Plus, Sp, y, Close);
    private static Formula Conj(params Formula[] xs)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) parts.Add(F.Seq(Sp, Land, Sp));
            parts.Add(F.Seq(Open, xs[i], Close));
        }
        return F.Seq(parts.ToArray());
    }
    private static Formula WithMeasurable(Formula type, Formula body) =>
        F.Seq(OpenBracket, A("MeasurableSpace", type), CloseBracket, Sp, body);
    private static Formula Let(string name, Formula value, Formula body) =>
        F.Seq(N("let"), Sp, N(name), Sp, Colon, Eq, Sp, value, Sp, N("in"), Sp, Open, body, Close);
}
