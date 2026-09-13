using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeBoxBidirectionalHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered mixed-register words have a shared-state semantics and an exact product profile.",
        H("Bidirectional Prime-Box Horizon"),
        Blocks(
            Paragraph(Text(
                "A command specifies a register and either multiplication or exact division. "
                + "The initial state is one capacity-bounded exponent tuple. Commands retain "
                + "their order within each register, while different registers act independently.")),
            Describe.Lean(
                DescribeId.Create("prime-box-chronological-guard-transport"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon.chronological_legality"),
                H("One joint chronological run, not independent edge witnesses"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("jointRunIsDefined"), Sp, Eq, Sp, F.Id("allOrderedLocalRunsAreDefined")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the mixed command list transports the actual repository "
                    + "partial runner through coordinate updates. A local failure forces a "
                    + "joint failure; a successful update changes only that register. This "
                    + "proves that the same initial tuple witnesses the entire history."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-box-exact-bidirectional-profile"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon.mixed_word_profile_classification"),
                H("Exact cardinality at every capacity vector and every horizon"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("profileCard"), Sp, Eq, Sp, D(1), Sp, Plus, Sp,
                    F.Id("product_i(min(a_i,2H)+1)")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Projecting a mixed word onto one register never increases its "
                        + "length. Conversely, every single-register word can be lifted to "
                        + "a mixed word using that register alone. These two constructions "
                        + "prove the exact product response kernel. Coordinate-wise "
                        + "surjectivity realizes every claimed profile, and finite product "
                        + "cardinality gives the displayed count including rejection.")),
                    Paragraph(Text(
                        "For the original capacities (4,2,1,1), counts are 2,37,61 at "
                        + "horizons 0,1,2. The target remains guard legality. The number of "
                        + "full live states has not fallen from 60; the availability of "
                        + "division shortens distinguishing experiments. Invalid attempts "
                        + "are observed as failure, not silently removed from the domain. "
                        + "No sparse base-4 DFAO conjecture is claimed solved."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/BoundedPrimeHorizon")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/PrimeCapacityHorizon"))
        ]));
}
