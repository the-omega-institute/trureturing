using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualExactSupportPruningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualExactSupportPruning.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact actual-support pruning retains every nominal state and transports each actual prefix into a complete finite table.",
        H("Exact Support Pruning and Nominal Table Coverage"),
        Blocks(
            Paragraph(Text("The actual source budget and the finite literal-address packing envelope are separate parameters. Queries outside the actual support become false halts; nominal caches are filtered without altering stored raw replies or order. Actual state visits, reports, cache values and actions remain unchanged. The original paired relation proves coarse factorization for the new total history semantics, including impossible histories.")),
            Def("ActualSupport", "Actual literal support", "Every query made at an actual prefix belongs to the specified finite set. This condition does not restrict unreachable rows."),
            Def("supportCache", "Raw cache projection", "Filter only by literal address membership, preserving chronology and four-valued replies."),
            Def("supportAction", "Supported row action", "Retain halt rows and supported query rows; replace other queries by false halts."),
            Def("supportObserver", "Pruned complete observer", "The complete nominal carrier and raw successor table are retained, with projected actions and caches."),
            Def("SupportPruningContract", "Exact pruning contract", "The two observers have exactly the same actual prefixes and rows; actual actions, caches and finite runs are preserved, and admissibility remains valid."),
            Theorem("support_pruning_contract", "Exact actual-support pruning", "Every admissible observer whose actual requests lie in the specified support satisfies the exact pruning contract. State observations transported by the identity retain their actual values."),
            Def("supportWidth", "Finite packing envelope", "One plus the maximum address length in the finite support; it is independent of the source budget."),
            Def("prescribedSupport", "Prescribed trace support", "The union of the distinct literal addresses in all prescribed terminal traces on the original bounded source domain."),
            Def("ExactTraces", "Prescribed raw runs", "Each allowed source has the prescribed full raw trace and terminal bit. Additional phase observations are not part of this predicate."),
            Theorem("exact_competitor_table_coverage", "All exact competitors have finite tables", "Every admissible exact-trace competitor has a native table on its full nominal cardinality with Qπ-only actions and caches. Under the state bijection it preserves all actual prefixes, actions and caches, the prescribed complete raw traces, and admissibility for the original source budget. This is representation of every competitor, not a quotient of one selected behavior table."),
            Paragraph(Text("This result supplies support pruning and nominal table coverage. It does not provide the original compileRaw phase-label parser, finite prescribed-prefix acceptance checks, the explicit route/verifier/acquisition horizon, or the marked and unmarked minimum and price formulas."))
        )));
    private static DocumentBlock Def(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-exact-support-pruning-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-exact-support-pruning-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
