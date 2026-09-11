using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Observation;

internal sealed class HistoryPayloadFactorizationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A summary recovers a payload exactly when the payload is constant on its fibers. "
            + "Global admission and complete local completion sets are two such payloads.",
        H("History Payload Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("payload-factorization"),
                DeclarationHandle.Create(Module + "ker_beta_subset_ker_payload_iff_unique_factorization"),
                H("Unique recovery on the realized image"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("ker", F.Id("beta")), Sp, Subseteq, Sp, Call("ker", F.Id("P")),
                    Sp, Iff, Sp, Factor(F.Id("beta"), F.Id("P"), F.Id("Z"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source, summary, and payload carriers have independent universes and may "
                        + "be empty. The factor is defined only on realized summary values. "
                        + "Existence and uniqueness follow by applying the split-surjection "
                        + "factorization theorem to the canonical range map and its section."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("global-admission"),
                DeclarationHandle.Create(Module + "global_admission_factorization"),
                H("Admission on complete raw global records"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Factor(F.Id("beta"), Call("admissionIndicator", F.Id("J"), F.Id("K")),
                        F.Id("Bool")), Close, Sp, Iff, Sp,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("J"), Comma,
                    Sp, Call("beta", F.Id("x")), Sp, Eq, Sp, Call("beta", F.Id("y")), Sp, To,
                    Sp, Open, F.Id("x"), Sp, InMacro, Sp, F.Id("K"), Sp, Iff, Sp,
                    F.Id("y"), Sp, InMacro, Sp, F.Id("K"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The domain is the subtype J, the raw global join. Its Boolean payload is "
                        + "the indicator of K restricted to J. The actual worlds are J intersect K."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("whole-global-fibers"),
                DeclarationHandle.Create(Module + "global_admission_iff_union_fibers"),
                H("Actual worlds are a union of whole restricted fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem identifies J intersect K with the image in the ambient record "
                        + "carrier of all complete J-records sharing a summary with an admitted "
                        + "J-record. This equality is equivalent to unique admission factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("factored-test"),
                DeclarationHandle.Create(Module + "admission_factor_test"),
                H("The recovered admission test remains a constraint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each complete raw record, the recovered Boolean test is true exactly "
                        + "when the record belongs to J intersect K. Factorization does not "
                        + "assert that the test is constantly true or authorize removing it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-assignment"),
                DeclarationHandle.Create(Module + "assignment_eq_empty"),
                H("Canonical empty assignment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The QI-JOIN empty component is identified with the canonical empty assignment; "
                        + "the dependent Value family and empty carrier remain intact."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-record-bridge"),
                DeclarationHandle.Create(Module + "mem_completion_payload_iff"),
                H("Completion payloads use complete compatible records"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An assignment supplies a value for every variable in its scope and "
                            + "requires no value outside that scope. The raw join consists of "
                            + "assignments whose restriction to each node lies in that node's "
                            + "local relation. The complement join also enforces consistency "
                            + "of variables shared between its components.")),
                    Paragraph(Text(
                        "The completion payload contains precisely those complete complement "
                            + "records matching the entire overlap assignment and whose union "
                            + "with the component record belongs to K. Membership is equivalent "
                            + "to one admitted raw global record having both specified "
                            + "restrictions. The restriction maps and compatible union are explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-factorization"),
                DeclarationHandle.Create(Module + "local_completion_factorization"),
                H("Recovery of the entire local completion set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The payload codomain is the power set of the complete complement join. "
                        + "It factors uniquely through the realized component summary exactly "
                        + "when equal summaries give equal completion sets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-global-tests"),
                DeclarationHandle.Create(Module + "local_completion_global_tests"),
                H("Global-record pointwise completion tests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each summary fiber and complete complement record, completion membership "
                        + "is characterized by existence of an admitted complete raw global record "
                        + "with both exact restrictions. This is the preregistered live consumer of "
                        + "mem_completion_payload_iff; its path uses the pinned dependent-function "
                        + "sheaf gluing owner. The factorization and local-tests companions do not "
                        + "consume this bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-tests"),
                DeclarationHandle.Create(Module + "local_completion_tests"),
                H("The equivalent pointwise completion tests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set equality is equivalent to agreement of the membership test for "
                            + "every complete complement record. Each test includes both full "
                            + "boundary compatibility and membership of the union in K.")),
                    Paragraph(Text(
                        "BoundaryOutputRetention names the additional requirement for later "
                            + "gluing: equal summaries preserve the entire boundary and every "
                            + "specified raw result on compatible complete complements. Results "
                            + "are read on the raw global join. Payload factorization alone "
                            + "does not establish that requirement or gluing congruence.")),
                    Paragraph(Text(
                        "Source identifiers, dependency sets, and other requested payloads "
                            + "use the same arbitrary-target kernel criterion. Preserving a "
                            + "result image by existential witnesses is a separate contract; "
                            + "it does not recover a discarded payload."))),
                DescribeRole.Theorem))));

    private static Formula Factor(Formula summary, Formula payload, Formula target) => Seq(
        Exists, Bang, Sp, F.Id("phi"), Colon, Sp, Call("range", summary), Sp, To, Sp,
        target, Comma, Sp, payload, Sp, Eq, Sp, F.Id("phi"), Sp, Circ, Sp,
        Call("rangeFactorization", summary));
}
