using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalLimit.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual proper-limit predecessor with original whole born packs and retained fusion certificates",
        H("Literal ordinal limit predecessor"), Blocks(
            Paragraph(Text("Let omega<l<omega-one, let l be a successor-limit ordinal, and let H be the actual strict Prefix(l). The Archive contains only previously born rows omega<=r<l: exhaustive support-family enumerations U, the originally launched V, and exhaustive entire legal signed enumerations nu with every Label below omega-one. It retains PastBirths(l), all historical I/J sets, and the actual onto base invariant at stage omega. The construction assumes H.Laws of the explicitly bound Archive.data; it assumes neither a next predecessor nor a final history.")),
            Describe.Lean(DescribeId.Create("limit-archive-data"),
                DeclarationHandle.Create(Owner + "data"), H("Bind the actual old archive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Data.I and Data.J are the archived sets. At every born row, Data.V is the very same saved support family and Data.nu is the very same whole signed enumeration. Data.N(r,d,false/true) reads slots zero/one from the original entry at succ(max(r,d)). Since r,d<l, max(r,d)<l; no limit-stage birth is invented. Values outside born row domains carry no obligations."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-limit-prefix"),
                DeclarationHandle.Create(Owner + "literalPrefix"), H("Append the literal limit carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the actual extension E of H, literalPrefix(H,E) has type Prefix(succ(l)). Each old carrier is exactly H.carrier at the same ordinal, with only the dependent index proof changed. The top carrier is H.limitCarrier, the subset of Cube(l) whose restriction lies in every old carrier. Every transition is literal coordinate restriction. Closedness is the intersection of inverse images of the old closed sets; nonemptiness and onto restrictions use E.inhabited and E.onto. No extra onto premise is accepted."))), DescribeRole.Definition),
            Paragraph(Text("The output has type SignedOrdinalSuccessor.Predecessor(literalPrefix(H,E),omega<=l). Its old rows are exactly omega<=r<l. U, V and nu retain the original whole packs through the exact old-carrier equality, including the original onto proofs. The birth archive is unchanged. I and J are E.I and E.J on those old rows. A, B and C consume E with the identical arrival reservoirs. For coordinate c<r, equality of the row restrictions directly gives equality of coordinate c; for r<=c, E.E supplies the conclusion.")),
            Paragraph(Text("For every arbitrary sequence of SignedMeasure on the actual top carrier, properMetric makes the compact limit space metrizable because the coordinate ordinal is countable. The finite positive and negative Jordan parts are automatically regular. Package each original signed measure unchanged as RegularSigned, apply E.F, and forget only the regularity and norm clauses required by the predecessor API. The base restriction is onto by composing E.onto at the genuine stage omega with the archive's earlier base invariant. No common limit before all sequences is asserted: the quantifiers are forall s exists mu.")),
            Describe.Lean(DescribeId.Create("limit-whole-archive-readback"),
                DeclarationHandle.Create(Owner + "predecessor_whole_readback"), H("Unchanged whole archive labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every old row of the actual limit predecessor, its entire U, V and nu are heterogeneously equal to the same archive row's U, V and nu on the unchanged literal carrier. All labels are retained, including labels not yet eligible for J."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("construct-limit-event"),
                DeclarationHandle.Create(Owner + "construct"), H("Retain the actual limit event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("construct takes Archive A, IsSuccLimit(l), and H.Laws(A.data), and invokes exists_joint_proper_limit_extension once. Result.extension retains that very Extension; Result.extended and Result.predecessor construct the literal prefix and predecessor from it. The event exposes exact old-carrier and top-carrier equalities, unchanged births, exact predecessor I/J readbacks, and exact born Data.N/V/nu equations. In particular extension.DI/DJ relate the new sets to all prior eligible sets, and extension.F retains its regular norm-at-most-one output. These facts must be read from the event for a global history: Predecessor alone has neither DI/DJ nor the full proper-F conclusion.")),
                    Paragraph(Text("This is a local construction for the well-founded ordinal recursion. It invents no birth at the limit, imposes no new CH, regularity, convergence or final-history premise, and does not establish the full CH construction or solve Problem 8.2."))), DescribeRole.Definition))));
}
