using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class MarkedRibbonErasureDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recorded deletion and recordless erasure on a fixed phase graph for a literal marked ribbon.",
        H("Recorded deletion and recordless erasure on a fixed ribbon phase graph"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-ribbon-two-deletions"),
                DeclarationHandle.Create(Owner + ".actual_ribbon_two_deletions"),
                H("One fixed chart controls recorded deletion and recordless erasure"),
                StatementSource.FromAuthor(RecordedStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose a signed spanning-forest chart for each physical flag component once. Its binary pairing is the adjacency between two distinct banks; diagonal twist entries are ordinary cross-bank edges. The selected mask only chooses which coordinates of the prebuilt phase graph are retained. Pauli Z feed-forward cancels the two mixed phases for every available computational-basis deletion outcome.")),
                    Paragraph(Text("The theorem combines the exact recordless coordinate entry with the purity of the outcome-conditioned left marginal. The trace of the square of that marginal is the relative size of the kernel of the restricted pairing. The binary Cohn–Lempel identity and literal state switch turn the product of these purities, multiplied by the two-power of the component and selected-band count, into the exact two-power of the original boundary-circle count. The phase graph is block diagonal across disconnected components. This is not an operational sample-complexity or Jones-normalization claim."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("erased-coset-corrected"),
                DeclarationHandle.Create(Owner + ".erased_coset_corrected"),
                H("Exact retained phase state within each recordless erasure coset"),
                StatementSource.FromAuthor(ErasedStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The mixed graph-state partial trace cancels all entries with distinct cross-phase syndromes by binary character orthogonality. Each surviving syndrome block is a subnormalized pure graph-phase block on the two kernels; explicit local signs remove the coset representatives. The proof operates on the normalized rank-one computational-basis projector before erasure, not on an assumed rank oracle.")),
                    Paragraph(Text("If the two cross-couplings are injective, the retained density is completely diagonal regardless of the retained pairing. Thus this zero-record operation has genuinely different information content from recorded deletion. Standard pure graph-state cut rank and Pauli deletion are due to Hein, Eisert and Briegel, Phys. Rev. A 69, 062311 (2004); the bridge here accounts for the signed literal ribbon and exact mixed erasure blocks."))),
                DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier q, string n, Formula t, Formula b) =>
        new Formula.Bind(q, FormulaIdentifier.Create(n), t, b);
    private static Formula All(string n, Formula t, Formula b) => Bind(FormulaQuantifier.ForAll, n, t, b);
    private static Formula Ex(string n, Formula t, Formula b) => Bind(FormulaQuantifier.Exists, n, t, b);
    private static Formula RecordedStatement()
    {
        var r = F.Id("R"); var c = F.Id("C"); var s = F.Id("s");
        return Disp(All("R", Call("FiniteLiteralMarkedSignedRibbons"),
            Ex("C", Call("ExtractedSignedCharts", r),
                All("s", Call("ChartStateMasks", c),
                    Equal(Call("ObservedRecordedPurityAndRecordlessEntries", c, s),
                          Call("LiteralBoundaryPowerAndSyndromePhaseEntries", r, c, s))))));
    }
    private static Formula ErasedStatement()
    {
        var g = F.Id("G"); var v = F.Id("v");
        return Disp(All("G", Call("FourBinaryPhaseBlocks"),
            All("v", Call("TranslatedSyndromeKernelCoordinates", g),
                Equal(Call("LocallyCorrectedErasedEntry", g, v),
                      Call("PurePhaseEntryWeightedBySyndrome", g, v)))));
    }
}
