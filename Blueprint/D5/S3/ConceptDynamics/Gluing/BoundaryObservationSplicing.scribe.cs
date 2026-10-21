using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class BoundaryObservationSplicingDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible dependent raw records have a unique splice with the prescribed union "
            + "assignment. Two complete-context replacements preserve a retained global output, "
            + "and arbitrary summaries define a partial observation relation.",
        H("Boundary Observation Splicing"),
        Blocks(
            Paragraph(Text(
                "A node component A carries a dependent rawJoin record on the union of its local "
                    + "scopes. For disjoint components A and B, overlapScope is the complete variable "
                    + "carrier shared by their scopes. The left and right overlap boundaries are the "
                    + "restrictions of the two records to this same carrier. The splice assignment uses "
                    + "the left value on the left scope and the right value elsewhere; agreement on the "
                    + "overlap makes this independent of the branch.")),
            Entry("overlapScope", "shared-scope", "Shared component scope",
                "The shared variable carrier is U_A intersect U_B.", DescribeRole.Definition),
            Entry("overlapBoundaryLeft", "left-overlap-boundary", "Left overlap restriction",
                "A left record is restricted to U_A intersect U_B.", DescribeRole.Definition),
            Entry("overlapBoundaryRight", "right-overlap-boundary", "Right overlap restriction",
                "A right record is restricted to U_A intersect U_B.", DescribeRole.Definition),
            Entry("spliceAssignment", "pointwise-splice", "Pointwise partial splice",
                "For x in U_{A union B}, use a(x) when x is in U_A and b(x) otherwise. The latter branch is defined because every x in U_{A union B} lies in U_A or U_B.", DescribeRole.Definition),
            Entry("compatible_splice_unique", "compatible-splice-unique", "Unique compatible raw join",
                "For disjoint A and B, if the two complete overlap restrictions agree, the pointwise splice is a rawJoin record on A union B and is the unique rawJoin record with that value function. Empty local scopes and empty local relations remain allowed; the theorem is conditional on the displayed compatible pair.", DescribeRole.Theorem),
            Entry("two_context_output_eq", "two-context-output-equality", "Two complete-context substitutions",
                "Let A and B be disjoint. Suppose each local summary retains its full boundary and every specified output G against every complete compatible complement. Two global raw records with equal A summaries, equal B summaries, and identical restrictions outside A union B have the same G output. First replace the A record while keeping its complete complement. The intermediate record keeps B unchanged; on the complement of B it agrees with the final record, by combining its A restriction with the common outside restriction. The B replacement then gives the second output equality. BoundaryOutputRetention is an explicit hypothesis; it is not inferred here for arbitrary summaries.", DescribeRole.Theorem),
            Entry("spliceGraph", "partial-splice-graph", "Partial observation graph",
                "The graph contains ((q_A(a),q_B(b)),q_C(a union b)) exactly for pairs whose complete overlap restrictions agree. Its domain is therefore a partial domain of summary pairs.", DescribeRole.Definition),
            Paragraph(Text(
                "For local summaries q_A and q_B, assume equality of summaries preserves the "
                    + "corresponding complete overlap restriction. If a and b initially agree on the "
                    + "overlap, and q_A(a)=q_A(a') and q_B(b)=q_B(b'), symmetry and transitivity of "
                    + "equality give agreement of a' and b'. This conditional observation uses the "
                    + "overlap-retention assumptions; it does not derive them from observational "
                    + "equivalence or prove that the two union summaries agree.")),
            Paragraph(Text(
                "The relation above does not assert a well-defined operation on observation "
                    + "quotients. That additionally requires preservation of the full union boundary and a "
                    + "bridge from the specified observation equivalence to the retention hypotheses. Its image "
                    + "is not identified here with every union observation. Restriction and "
                    + "reconstruction of arbitrary union records, finite contraction with independence "
                    + "of order, the unique empty root context, and the descended root map preserving "
                    + "the complete joint output image remain unproved here.")))));

    private static DocumentBlock Entry(string declaration, string id, string title,
        string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
