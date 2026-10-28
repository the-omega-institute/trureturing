using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalSuccessorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalSuccessor.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary ordinal successor with actual legal births and permanent arrival readback",
        H("Ordinal successor and arrival births"), Blocks(
            Paragraph(Text("The predecessor consists of one literal Prefix through stage a, where omega is at most a and a is below omega-one. Its actual current carrier maps onto Cube(omega). All old rows have exhaustive support and legal regular signed enumerations; old I and J have their strict born domains. Old N is read from the entry at the unique stage succ(max(row,label)). Only these partial predecessor laws are assumed. No complete history or extension supplier is an input.")),
            Describe.Lean(DescribeId.Create("executed-ordinal-successor"),
                DeclarationHandle.Create(Owner + "exists_successor"), H("Executed ordinary successor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under CH, the construction first enumerates all current support families and clopens. Launch(row,supportIndex) then pulls back the chosen support family, using the newly chosen current enumeration when launch.row equals a. A genuine exhaustive enumeration of all legal signed measures on this launched row is chosen before Treatment(row,label). Launch indices and signed sequence labels are separate typed fields. Actual proper ordinal countability constructs an injective row code with code(a)=0 and an auxiliary old-label schedule with infinite fibres at each parity.")),
                    Paragraph(Text("The proof applies SignedSplitSuccessor.exists_measured_dynamic_split to the actual K(a), its literal coordinate functions, and literal onto restrictions. The new row projection is the identity. The same executed split supplies final I and J, inherited N on old rows and labels, auxiliary parity reservoirs on the new row for old labels, and final-I residual reservoirs on every row for label a. SignedSuccessorCoordinates.exists_successor_coordinates inserts this split in Cube(succ(a)) and extends the same Prefix without replacing old carriers. A through-a arrival pack is returned together with all-pair readback and exact preservation of every earlier birth entry.")),
                    Paragraph(Text("The Result retains A, B, C, exact one-step refinement of old I and J, whole-support fibre E, and regular common every-choice signed F on its certified split presentation. It separately retains quantitative G with the same StrictMono column index. This local result does not construct the ordinal schedule, delayed execution with an exposed increasing target index, well-founded history, same-family proper limits, final omega-one carrier, anti-homeomorphism, Grothendieck property, or entire signed dual ball. The same executed coordinate equivalence also transports common F and whole-support E to the literal cube."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arrival-birth-readback"),
                DeclarationHandle.Create(Owner + "birth_readback"), H("Permanent birth readback"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every omega<=row<=a, label<=a and parity, readback from the enlarged partial birth history at succ(max(row,label)) equals the reservoir in the executed Result. If both indices are old, the predecessor's permanent entry is read. If the row is a and the label is old, the executed new-row parity output is read. If the label is a, including the doubly new pair, the executed residual output is read. No value for an unborn row or label is inserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arrival-retains-old-entries"),
                DeclarationHandle.Create(Owner + "arrival_retains"), H("Old entries are unchanged"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The entire entry for every outgoing stage b<a remains equal to the predecessor entry, on exactly its born domain max(row,label)=b. The newly available arrival at a+1 is supplied as additional data; it is never claimed to be already present in a strict prefix ending at a+1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-common-f"),
                DeclarationHandle.Create(Owner + "literal_f"), H("Common every-choice F on the literal cube"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each original row r and label d, one signed measure mu on the literal successor has total variation at most one and regular positive and negative Jordan parts. This mu is chosen before all sequences of signed norm-one lifts of the unchanged Q.measure(r,d,n). Every such sequence converges weak-star to mu along the original R.J(r,d).")),
                    Paragraph(Text("Choose the common split reference from Result.F and push it forward once through Result.coordinates.equiv. The images of its mutually singular Jordan parts form the image signed measure's Jordan decomposition; the homeomorphism preserves their regularity and total variation. Pull each arbitrary literal lift backward through the inverse of that same equivalence. Its projection and norm remain unchanged. Evaluating a continuous test after transport equals evaluating its composition with the homeomorphism before transport, so the original common convergence yields literal convergence. No measure label, subsequence or reference limit is reselected."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-fibre-e"),
                DeclarationHandle.Create(Owner + "literal_e"), H("Whole-support E for every literal coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each row and each coordinate below succ(a), eventually along the original I(row), any two points above the same point of the original support clopen have equal coordinate values. Old coordinates use their clopen truth sets in Result.E and the exact insertion equation. Coordinate a uses the sheet equality from that same E and the exact inverse-sheet equation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-quantitative-g"),
                DeclarationHandle.Create(Owner + "quantitative_g"), H("Quantitative G on the literal cube"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Result.quantitative_transport transfers any predicate of the split-sheet signed value through this same coordinate equivalence, preserving the original whole measure and column index. It is consumed both here and by the strong delayed certificate. The literal successor clopen tests the newly inserted ordinal coordinate a. Pushforward along the inverse homeomorphism preserves total variation and the original projection equation. For every q and every signed norm-one lift of the original treated sequence at the same increasing column index, even q has clopen value strictly greater than one sixth and odd q has value zero. This quantitative certificate is separate from Prefix.Laws and from any nonconvergence assertion."))), DescribeRole.Theorem))));
}
