using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class TwoStateLocalityIncrementalPreservationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation."
            + "two_state_locality_yields_incremental_preservation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-state locality preserves a property outside a changed dependency set.",
        H("Two-State Locality and Incremental Preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-state-locality-yields-incremental-preservation"),
                DeclarationHandle.Create(Declaration),
                H("Two-state locality yields incremental preservation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Changed(bytes,s,t) is the set of artifacts whose bytes differ. Local "
                            + "quantifies over every pair of states and requires equality on x "
                            + "together with both states' actual read sets.")),
                    Paragraph(Text(
                        "For the fixed states, dep over-approximates the union of both actual "
                            + "read sets at every artifact. Disjointness from Changed therefore "
                            + "makes every dependency used at x byte-equal.")),
                    Paragraph(Text(
                        "The unchanged premise supplies byte equality at x itself. Those equalities "
                            + "discharge the locality antecedent and yield the stated equivalence; "
                            + "the equivalence is not an assumption."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Apply(
        Formula function, Formula first, Formula second, Formula third) =>
        Seq(function, Open, first, Comma, Sp, second, Comma, Sp, third, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula artifact = F.Id("Artifact");
        Formula value = F.Id("Value");
        Formula bytes = F.Id("bytes");
        Formula reads = F.Id("reads");
        Formula property = F.Id("P");
        Formula first = F.Id("s");
        Formula second = F.Id("t");
        Formula dep = F.Id("dep");
        Formula x = F.Id("x");
        Formula proposition = F.Id("Prop");
        Formula artifactSet = Call("Set", artifact);
        Formula changed = Apply(F.Id("Changed"), bytes, first, second);
        Formula readUnion = Call(
            "union", Apply(reads, first, x), Apply(reads, second, x));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, artifact, Comma, Sp, value,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            RowBreak, Grp(),
            bytes, Colon, Sp, Arrow(state, Arrow(artifact, value)), Comma, Sp,
            reads, Colon, Sp, Arrow(state, Arrow(artifact, artifactSet)), Comma,
            RowBreak, Grp(),
            property, Colon, Sp, Arrow(state, Arrow(artifact, proposition)), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, state, Comma, Sp,
            dep, Colon, Sp, Arrow(artifact, artifactSet), Comma,
            RowBreak, Grp(),
            Apply(F.Id("Local"), bytes, reads, property), Sp, Rightarrow, Sp,
            Grp(Forall, Sp, x, Colon, Sp, artifact, Comma, Sp,
                readUnion, Sp, Subseteq, Sp, Apply(dep, x)), Sp, Rightarrow,
            RowBreak, Grp(),
            x, Sp, Neg, InMacro, Sp, changed, Sp, Rightarrow, Sp,
            Call("Disjoint", Apply(dep, x), changed), Sp, Rightarrow,
            RowBreak, Grp(),
            Open, Apply(property, first, x), Sp, Leftrightarrow, Sp,
            Apply(property, second, x), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
