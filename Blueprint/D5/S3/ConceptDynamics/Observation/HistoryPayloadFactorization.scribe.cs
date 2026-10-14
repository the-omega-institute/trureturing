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
            new DocumentBlock.Section(H("Clocks on realized observation fibers"), Blocks(
                Paragraph(Text(
                    "Let X be any set of complete finite histories, R a readout into Y, and t a "
                    + "natural-valued clock. The realized-image factorization applies with beta = R and payload "
                    + "= t: a unique function on range(R) recovers t precisely when R(x) = R(y) implies t(x) = "
                    + "t(y). This includes an empty X; no arbitrary output at an unrealized value of Y is "
                    + "required.")),
                Paragraph(Text(
                    "For serial group-valued gate readout, the literal word [g, inverse(g)] and the empty "
                    + "word both have product one, but their lengths are two and zero. Thus product readout "
                    + "alone does not determine length. The joint readout (R,t) determines both components. If "
                    + "Q has decoders r and c with R = r composed with Q and t = c composed with Q, then z maps "
                    + "to (r(z),c(z)) is a decoder for the joint readout. This universal property does not "
                    + "assert that the joint readout is injective on histories.")))),
            new DocumentBlock.Section(H("Multiplicity at a fixed clock value"), Blocks(
                Paragraph(Text(
                    "Let c assign r distinct literal words of width two to the alphabet of neutral blocks. "
                    + "Represent a width-two word by a function on Fin(2), and a sequence of k choices by s on "
                    + "Fin(k). The history at position 2i+j is c(s(i))(j). The product equivalence between "
                    + "Fin(k) times Fin(2) and Fin(2k), followed by List.ofFn, represents precisely the "
                    + "concatenation of these blocks; List.ofFn_mul supplies the equality with the flattened "
                    + "block list.")),
                Paragraph(Text(
                    "Equality of the histories gives equality at every position 2i+j, hence equality of each "
                    + "selected block, and injectivity of c gives equality of s. There are r to the power k "
                    + "choices. All histories have length 2k. If the product readout of each block is the "
                    + "monoid identity, List.prod_flatten makes every concatenation neutral. These facts use "
                    + "literal distinctness of blocks, independently of their common operator value.")),
                Paragraph(Text(
                    "On this family, a memory M that reconstructs history together with the constant product "
                    + "and clock must be injective. Its realized range has at least r to the power k elements. "
                    + "A fixed b-bit memory has 2 to the power b values, so b is at least the ceiling of k "
                    + "times log base two of r. The bound concerns exact recovery on the entire family.")))),
            new DocumentBlock.Section(H("Support-covered assignment gluing"), Blocks(
                Paragraph(Text(
                    "Let V index possibly dependent value types. For each constraint c, let K(c) be its "
                    + "support and let its allowed relation be a predicate on complete assignments on K(c). An "
                    + "assignment on A is legal when every constraint with support contained in A holds. "
                    + "Suppose subsets U(i) cover A, each local assignment is legal, and the assignments agree "
                    + "pointwise on all overlaps.")),
                Paragraph(Text(
                    "The sheaf of dependent functions on the discrete space V supplies the unique underlying "
                    + "assignment on A. If each support K(c) contained in A lies entirely inside some U(i), its "
                    + "restriction equals the corresponding local restriction, so local legality gives the "
                    + "constraint on the glued assignment. No pairwise reduction of a constraint is used. The "
                    + "argument works even for infinite supports when the same containment hypothesis holds; "
                    + "finite supports give the stated local-constraint setting.")),
                Paragraph(Text(
                    "Support containment is essential. On three Boolean coordinates impose that their "
                    + "exclusive-or is false. The three regions obtained by omitting one coordinate cover all "
                    + "positions, but none contains the ternary support. Restricting (false,false,true) to "
                    + "those regions gives legal local records with matching overlaps, while their unique union "
                    + "violates the ternary constraint. The general sheaf gluing condition is the standard one "
                    + "described in the Stacks Project, tag 006S.")))),
            new DocumentBlock.Section(H("Linear boundary recovery"), Blocks(
                Paragraph(Text(
                    "Let M and P be linear maps on a finite-dimensional vector space over a field, with legal "
                    + "interior S equal to kernel(M) and boundary readout the restriction of P to S. "
                    + "LinearMap.injective_domRestrict_iff identifies injectivity with disjointness of "
                    + "kernel(M) and kernel(P), equivalently their intersection is zero.")),
                Paragraph(Text(
                    "The paired map x maps to (M(x),P(x)) has kernel equal to that intersection by "
                    + "LinearMap.ker_prod. Rank-nullity therefore identifies injectivity on S with full column "
                    + "rank of the vertically stacked matrix [M;P]. For domain K to the power n the rank is n. "
                    + "These equivalent conditions give uniqueness only for boundary values in P(S); they do "
                    + "not imply that P(S) is the entire boundary space. For a target function on S, the "
                    + "earlier realized-image factorization instead requires only that the target be constant "
                    + "on the boundary fibers.")))),
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
                DeclarationHandle.Create(Module + "rawJoin_empty"),
                H("Canonical singleton empty join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty raw join is exactly the singleton containing emptyAssignment, "
                        + "transported back along componentScope_empty. This proves membership "
                        + "and uniqueness for the dependent Value family without any inhabited "
                        + "value fiber or local relation premise."))),
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
                        + "with both exact restrictions. The membership equivalence uses the "
                        + "sheaf of dependent functions to construct the common assignment."))),
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
