using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FreshServiceRestartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FreshServiceRestart", H("Repeated acceptance on one fresh stream"), Blocks(
            Paragraph(Text("An iid external stream supplies candidates one at a time. The first accepted coordinate and the suffix strictly after it are semantic execution coordinates. Neither the search index nor the suffix is a retained machine register or a readable random tape. The fallback totalizes the zero-mass event of never accepting.")),
            Paragraph(Text("A first-hit event fixes a rejected prefix and one accepted candidate. Independence of disjoint coordinate sets factors its joint mass with any measurable suffix event. The rejected-prefix masses form a geometric series. Positive acceptance mass makes infinite rejection null, and summing the disjoint first-hit events gives the conditional accepted law times the unchanged iid suffix law.")),
            Paragraph(Text("Repeated services always consume the unused suffix of that same stream. Their prefix probabilities follow by induction from the joint restart identity. Equality of every finite prefix, followed by projective-limit uniqueness, identifies the complete infinite output measure. Countable intersection of the full-measure return events covers every repeated service.")),
            Paragraph(Text("RarePriorSerialExecution.repeated_fresh_bit_service applies this result to consecutive packets of seven external fair bits and relates the accepted candidates to the existing reset/bit/compare trajectory. This probability theorem does not implement a scanner or renderer, charge a complete machine snapshot, establish original COMPLETE membership or optimize an original inf-sup risk.")),
            Node("first-hit", "first_hit_some", "First hit characterization", "The selected index has an accepted candidate and every strictly earlier coordinate rejects."),
            Node("restart-law", "first_acceptance_restart", "Accepted value and untouched suffix", "First acceptance yields the conditional accepted value independently of the entire unused iid suffix."),
            Node("repeated-law", "repeated_acceptance_law", "Whole repeated output law", "The complete repeated accepted sequence has the iid conditional-acceptance law, and every repeated service returns outside one null event."))));

    private static DocumentBlock.Describe Node(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);

    private static Formula Statement(string name)
    {
        var common = Seq(Q("A", N("Type")), Q("inst", App("MeasurableSpace", N("A"))));
        var args = Seq(Q("accept", App("Set", N("A"))), Q("fallback", N("A")));
        var probability = Seq(Q("mu", App("Measure", N("A"))), Q("hprob", App("IsProbabilityMeasure", N("mu"))));
        var hypotheses = Seq(App("MeasurableSet", N("accept")), Sp, To, Sp,
            App("mu", N("accept")), Sp, Neq, Sp, D(0), Sp, To, Sp);
        var iid = App("Measure.infinitePi", Seq(N("fun"), Sp, N("i"), Sp, Colon, Sp, Nat, Sp, Mapsto, Sp, N("mu")));
        var conditional = App("ProbabilityTheory.cond", N("mu"), N("accept"));
        var repeated = App("draws", N("accept"), N("fallback"));
        return name switch
        {
            "first_hit_some" => Seq(common, Q("accept", App("Set", N("A"))), Q("omega", Seq(Nat, Sp, To, Sp, N("A"))), Q("n", Nat),
                App("firstHit", N("accept"), N("omega")), Sp, Eq, Sp, App("some", N("n")), Sp, Iff, Sp,
                App("omega", N("n")), Sp, InMacro, Sp, N("accept"), Sp, Land, Sp,
                Forall, Sp, N("i"), Sp, Lt, Sp, N("n"), Sp, Comma, Sp, Neg, Sp,
                Open, App("omega", N("i")), Sp, InMacro, Sp, N("accept"), Close),
            "first_acceptance_restart" => Seq(common, probability, args, hypotheses,
                App("Measure.map", App("restart", N("accept"), N("fallback")), iid), Sp, Eq, Sp,
                App("Measure.prod", conditional, iid)),
            "repeated_acceptance_law" => Seq(common, Q("finite", App("Fintype", N("A"))),
                Q("singletons", App("MeasurableSingletonClass", N("A"))), probability, args, hypotheses,
                App("Measurable", repeated), Sp, Land, Sp, App("Measure.map", repeated, iid), Sp, Eq, Sp,
                App("Measure.infinitePi", Seq(N("fun"), Sp, N("i"), Sp, Colon, Sp, Nat, Sp, Mapsto, Sp, conditional)),
                Sp, Land, Sp, Open, N("ae"), Sp, N("omega"), Sp, N("under"), Sp, iid, Sp, Comma, Sp,
                Q("n", Nat), App("firstHit", N("accept"),
                    App("unused", N("accept"), N("fallback"), N("n"), N("omega"))), Sp, Neq, Sp, N("none"), Close),
            _ => N("Unknown")
        };
    }
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q(string name, Formula type) => Seq(Forall, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Sp, Comma, Sp);
    private static Formula App(string name, params Formula[] args)
    {
        var terms = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) terms.Add(Seq(Sp, Comma, Sp));
            terms.Add(args[i]);
        }
        terms.Add(Close);
        return F.Seq(terms.ToArray());
    }
    private static Formula N(string name)
    {
        var terms = new System.Collections.Generic.List<Formula>();
        var parts = name.Split('.');
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) terms.Add(Dot);
            terms.Add(Seq(Operatorname, Grp(F.Id(parts[i]))));
        }
        return F.Seq(terms.ToArray());
    }
    private static Formula Seq(params Formula[] items) => F.Seq(items);
}
