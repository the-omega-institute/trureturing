using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalRealizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SignedOrdinalRealization", H("One literal omega-one prefix"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalrealization-final-prefix"),
                DeclarationHandle.Create(Owner + "finalPrefix"), H("One literal omega-one prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The final Prefix reads each carrier from the same canonical well-founded run under CH. Below omega the carriers are full Boolean cubes. Closedness, nonemptiness, compatibility and onto restrictions are inherited from the actual later state and its coherence. There is no second recursion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signedordinalrealization-proper-data"),
                DeclarationHandle.Create(Owner + "properData"), H("Data at every proper cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Only proper countable cutoffs carry Data. Whole U, V and nu are read at the original row birth. Incoming I and J are read at their carrier stage. Permanent reservoirs are read from the original outgoing R at max(row,label), including at the last row of a successor slice."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signedordinalrealization-proper-laws"),
                DeclarationHandle.Create(Owner + "properLaws"), H("Original laws on all proper slices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All eligible A through F and DI/DJ hold at every proper cutoff, including successors. F uses the regular bounded incoming evidence retained by the actual state, from the previous outgoing R or the actual limit Extension."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-slice-carrier"),
                DeclarationHandle.Create(Owner + "slice_carrier"), H("The slice is literal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every proper slice has exactly the final Prefix carrier at the same ordinal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-carrier-read"),
                DeclarationHandle.Create(Owner + "carrier_read"), H("Every run carrier is preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every earlier carrier in an actual state equals the corresponding final Prefix carrier. Pairwise coherence makes the value independent of which later state is used to read it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-top-read"),
                DeclarationHandle.Create(Owner + "top_read"), H("The actual top carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At every stage from omega onward the final carrier is literally the top carrier of the canonical run state."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-initial-carrier"),
                DeclarationHandle.Create(Owner + "initial_carrier"), H("The original initial cubes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("At every coordinate at most omega the carrier is the full Boolean function space."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-whole-birth-read"),
                DeclarationHandle.Create(Owner + "wholeBirth_read"), H("The identical whole birth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The final whole birth is the actual newborn Q, transported solely across equality of the literal carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-whole-measure"),
                DeclarationHandle.Create(Owner + "whole_measure"), H("Original whole measure labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Each original label and natural index reads the identical signed measure in the actual whole birth, with the necessary heterogeneous equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-slice-nu"),
                DeclarationHandle.Create(Owner + "slice_nu"), H("Slice measures retain whole labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The signed measure in every proper slice equals the original whole birth measure. Labels need not be eligible at the cutoff to be preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-slice-j"),
                DeclarationHandle.Create(Owner + "slice_J"), H("Actual incoming J"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For eligible old rows and labels the proper Data J is exactly the actual incoming predecessor J at that carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-successor-carrier"),
                DeclarationHandle.Create(Owner + "successor_carrier"), H("The selected outgoing carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The carrier at succ(a) equals the coordinates.carrier of the same selected R at a."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-projection-factor"),
                DeclarationHandle.Create(Owner + "projection_factor"), H("Final projections factor literally"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Restriction between two proper carriers composed with final projection equals the earlier final projection."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-initial-onto"),
                DeclarationHandle.Create(Owner + "initial_onto"), H("Onto the initial countable cube"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The same final cube maps onto the full Boolean cube on omega by its original coordinate restriction. Compact inverse-limit lifting supplies a point above every initial function."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-slice-n"),
                DeclarationHandle.Create(Owner + "slice_N"), H("Permanent slice reservoirs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every born row and label pair in any proper slice reads the original permanent reservoir at their unique outgoing maximum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-reservoir-incoming"),
                DeclarationHandle.Create(Owner + "reservoir_incoming"), H("Original reservoirs at every eligible carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The permanent outgoing maximum reservoirs equal the actual incoming oldN at every eligible later carrier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedordinalrealization-launch"),
                DeclarationHandle.Create(Owner + "launch"), H("Actual cofinal support launches"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Each original support index is launched arbitrarily late. The newborn V at outgoing row a is the exact pullback of the original U along the same final Prefix restriction. Its archive is available at succ(a); support indices remain distinct from whole measure labels."))), DescribeRole.Theorem),
            Paragraph(Text("No final endpoint is asserted.")))));
}
