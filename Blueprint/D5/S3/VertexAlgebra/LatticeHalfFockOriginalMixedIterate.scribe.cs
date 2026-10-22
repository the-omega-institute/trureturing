using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockOriginalMixedIterateDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal Original Minus-One Mixed Iterate.",
        H("Literal Original Minus-One Mixed Iterate"),
        Blocks(
            Paragraph(Text("sourceCurrent is the existing ordinary Y applied to the literal zero-charge current state. The existing stateField_current and neutralField_ncoeff identify its original normalized modes. It is not a replacement descendant, native module action or assumed Jacobi law.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockoriginalmixediterate-sourcecurrent-ground-modes"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOriginalMixedIterate.sourceCurrent_ground_modes"),
                H("Actual original current modes on a charged source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("On e(a)=Finsupp.single a 1, the original minus-one mode is the literal sum of h(i) times Finsupp.single a X(i,0), the zero mode is B(h,a) times e(a), and every integer mode at least one vanishes. The ordinary neutral polynomial action on the unit proves these statements without truncating the carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockoriginalmixediterate-original-mixed-iterate-minus-one"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockOriginalMixedIterate.original_mixed_iterate_minus_one"),
                H("The original n=-1 specialization under actual Ytw"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The theorem uses the actual original sourceCurrent[-1] e(a) and sourceCurrent[0] e(a) inside existing Ytw. Its coefficient identity is the two finite physical half-current products with exponents E+2q+1-2k and E+2q+3+2k, for every signed q. The correction scalar q+1/2 is applied to the actual Ytw zero-mode source coefficient, not to a fictitious field. All higher original ground modes vanish as proved in the preceding theorem."))),
                DescribeRole.Theorem),
            Paragraph(Text("This proves the literal first-descendant n=-1 coefficient specialization only. Full twisted Borcherds or Jacobi, multi-oscillator permutation invariance, charged locality, complete moonshine, CFT, anomaly, fusion, string dynamics and AdS/CFT remain open. Four-slot source admission is unfinished; the Reg mirror preserves the full dependent scope and equivalent law without claiming declared_validated.")))));
}
