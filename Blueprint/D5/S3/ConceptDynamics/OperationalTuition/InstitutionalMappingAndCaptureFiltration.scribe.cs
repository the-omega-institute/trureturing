using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class InstitutionalMappingAndCaptureFiltrationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/OperationalTuition/"
            + "InstitutionalMappingAndCaptureFiltration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Append-only institution registration and T1-compliant event classification make "
            + "operational tuition monotone, decidable, and locally auditable.",
        H("Institutional Mapping and Capture Filtration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("institution-domains-grow-and-defects-are-decidable"),
                DeclarationHandle.Create(
                    Prefix + "institution_domain_monotone_and_defect_decidable"),
                H("Institution domains grow and defects are decidable"),
                StatementSource.FromAuthor(InstitutionMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An operational trajectory is a finite event list. A registration event "
                            + "adds its error class to the defined domain of the partial "
                            + "institution map, and list extension never removes that witness.")),
                    Paragraph(Text(
                        "The second conjunct is computational: defectDecision returns true "
                            + "exactly when the class occurred earlier and its institution was "
                            + "already registered. Thus the same-class recurrence violation is "
                            + "decidable without a private axiom."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capture-levels-filter-and-decreases-locate-defects"),
                DeclarationHandle.Create(
                    Prefix + "capture_ladder_filtration_and_t1_nondecreasing"),
                H("Capture levels filter and decreases locate defects"),
                StatementSource.FromAuthor(CaptureFiltrationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The threshold event sets are monotone from wall through gate to author: "
                            + "raising the threshold retains every event already admitted.")),
                    Paragraph(Text(
                        "For two occurrences of an already institutionalized class, either the "
                            + "later capture level is no lower or T1 marks that later occurrence "
                            + "as an institutional defect. The located-defect conclusion carries "
                            + "the exact prefix and suffix around the exceptional event.")),
                    Paragraph(Text(
                        "The T1 law is evidence stored in T1CompliantTrajectory, not a Lean axiom. "
                            + "A compiled finite witness realizes the exception branch with a "
                            + "gate-to-wall decrease."))),
                DescribeRole.Theorem))));

    private static Formula ListOf(Formula element) => Call("List", element);

    private static Formula EventOf(Formula errorClass) => Call("Event", errorClass);

    private static Formula TraceOf(Formula errorClass, Formula institution) =>
        Call("OperationalTrajectory", errorClass, institution);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula Singleton(Formula item) =>
        Seq(OpenBracket, item, CloseBracket);

    private static Formula AppendMany(params Formula[] lists)
    {
        Formula result = lists[^1];
        for (int index = lists.Length - 2; index >= 0; index--)
        {
            result = Call("append", lists[index], result);
        }

        return result;
    }

    private static Formula InstitutionMonotonicityFormula()
    {
        Formula errorClass = F.Id("C");
        Formula institution = F.Id("I");
        Formula earlier = F.Id("tau");
        Formula later = F.Id("upsilon");
        Formula history = F.Id("h");
        Formula current = F.Id("e");
        Formula trace = TraceOf(errorClass, institution);
        Formula eventType = EventOf(errorClass);
        Formula domainMonotonicity = Seq(
            Forall, Sp, earlier, Comma, Sp, later, Colon, Sp, trace, Comma, Sp,
            Call("IsTrajectoryPrefix", earlier, later), Sp, Rightarrow, Sp,
            Call("institutionDomain", earlier), Sp, Subseteq, Sp,
            Call("institutionDomain", later));
        Formula decisionCorrectness = Seq(
            Forall, Sp, history, Colon, Sp, ListOf(eventType), Comma, Sp,
            current, Colon, Sp, eventType, Comma, Sp,
            Call("defectDecision", history, current), Sp, Eq, Sp, F.Id("true"),
            Sp, Iff, Sp, Call("InstitutionalDefect", history, current));

        return Disp(Seq(
            Forall, Sp, errorClass, Comma, Sp, institution, Colon, Sp, F.Id("Type"),
            Comma, Sp, Typeclass("DecidableEq", errorClass), Comma, RowBreak, Grp(),
            Open, domainMonotonicity, Close, Sp, Land, RowBreak, Grp(),
            Open, decisionCorrectness, Close, Dot));
    }

    private static Formula CaptureFiltrationFormula()
    {
        Formula errorClass = F.Id("C");
        Formula institution = F.Id("I");
        Formula trajectory = F.Id("tau");
        Formula history = F.Id("h");
        Formula earlier = F.Id("e0");
        Formula middle = F.Id("m");
        Formula later = F.Id("e1");
        Formula suffix = F.Id("s");
        Formula eventType = EventOf(errorClass);
        Formula eventList = ListOf(eventType);
        Formula traceShape = Equal(
            Call("events", trajectory),
            AppendMany(
                history,
                Singleton(earlier),
                middle,
                Singleton(later),
                suffix));
        Formula established = Equal(
            Call("institutionEstablished", history, Call("errorClass", earlier)),
            F.Id("true"));
        Formula sameClass = Equal(
            Call("errorClass", earlier),
            Call("errorClass", later));
        Formula hypotheses = Seq(
            traceShape, Sp, Land, Sp, established, Sp, Land, Sp, sameClass);
        Formula outcome = Seq(
            Call("capture", earlier), Sp, Leq, Sp, Call("capture", later),
            Sp, Lor, Sp,
            Call("LocatedInstitutionalDefect", trajectory, later));
        Formula temporalClause = Seq(
            Forall, Sp, history, Comma, Sp, middle, Comma, Sp, suffix,
            Colon, Sp, eventList, Comma, Sp,
            earlier, Comma, Sp, later, Colon, Sp, eventType, Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(), outcome);

        return Disp(Seq(
            Forall, Sp, errorClass, Comma, Sp, institution, Colon, Sp, F.Id("Type"),
            Comma, Sp, Typeclass("DecidableEq", errorClass), Comma, RowBreak, Grp(),
            trajectory, Colon, Sp,
            Call("T1CompliantTrajectory", errorClass, institution), Comma, RowBreak, Grp(),
            Call("Monotone", Call("captureFiltration", trajectory)),
            Sp, Land, RowBreak, Grp(), Open, temporalClause, Close, Dot));
    }
}
