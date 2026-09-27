using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class LongestZeroSelectorResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact longest-run selection and zero-input direction response.",
        H("Longest-Zero Selection and Actual Responses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("family-selection"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/LongestZeroSelectorResponse.family_selection"),
                H("The first surviving long interval is the actual winner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix any natural r,p,R,e and parameter function h, with the whole gap word already "
                            + "read: p+span(familyGaps r h)<e. The strict past window is [e-R,e). candidates "
                            + "enumerates all endpoint pairs below e, tests completeness from the actual bit set, "
                            + "and retains exactly those whose left endpoint a satisfies e<=R+a.")),
                    Paragraph(Text(
                        "The score (b-a-1)(e+1)+b first maximizes interior length and then the closing "
                            + "endpoint b. Since every candidate endpoint is less than e, this scalar score "
                            + "implements the original length/latest-endpoint ordering. The theorem proves that "
                            + "longAnchor is either absent with an empty candidate set, or is a present interval of "
                            + "length at least three with strictly larger score than every other actual candidate.")),
                    Paragraph(Text(
                        "After an expired long interval is removed, the remaining candidates split into its "
                            + "length-one fillers and the shorter tail family. Every such filler starts before the "
                            + "following long interval; whenever it survives, that long interval also survives. "
                            + "Thus a filler cannot replace a winning long interval. Empty fillers may share the "
                            + "preceding and following one endpoint. Expiry is controlled by the left endpoint, not "
                            + "by a width-R queue of closing endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("direction-family"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Trajectories/LongestZeroSelectorResponse.direction_family"),
                H("Exact zero-continuation response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all r,h,p,R and n, the actual direction at e=p+span(familyGaps r h)+1+n equals "
                            + "responseModel r h R n. The original direction selects the actual maximum and "
                            + "transports from its closing endpoint using all zero bits in (b,e); it is zero if "
                            + "there is no candidate.")),
                    Paragraph(Text(
                        "The recursive formula uses (r+n) mod 2 while the first long interval survives, "
                            + "equivalently while span(familyGaps r h)+1+n<=R, and otherwise recurses to the "
                            + "shorter tail. For r=0 it is n mod 2 while 5+n<=R and is zero afterwards. The "
                            + "selector equality and transport identity are proved before using this formula.")),
                    Paragraph(Text(
                        "Each filler contributes an even number 2h(i) of zeros; each remaining long gap is "
                            + "odd. transport_suffix therefore gives the actual phase, including all consumed "
                            + "filler bits. Passing to the surviving tail changes neither those bits after its "
                            + "anchor nor their transport parity. The formula is a consequence of the source bits "
                            + "and selector, with no assumed switch schedule."))),
                DescribeRole.Theorem))));
}
