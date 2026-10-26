using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalInitialDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalInitial.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full Boolean cubes and the first ordinal predecessor",
        H("Actual initial cubes"), Blocks(
            Describe.Lean(DescribeId.Create("initial-full-cubes"),
                DeclarationHandle.Create(Owner + "H0"), H("Finite and omega cubes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("H0 is a Prefix(succ omega) whose carrier at every ordinal a<succ omega is the entire function space Coord(a) to Bool. Each carrier is closed and contains the constant-false point. Every transition is SignedProperLimit.restrict on the literal coordinates. Surjectivity extends a Boolean function by false outside its original coordinate domain; it is proved for every lower-stage pair, including the finite stages and omega."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial-omega-predecessor"),
                DeclarationHandle.Create(Owner + "predecessor"), H("Empty-history omega predecessor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("predecessor constructs SignedOrdinalSuccessor.Predecessor H0 (le_refl omega) without any predecessor assumption or CH. Properness is omega<omega-one. The current full omega cube maps onto Cube(omega) by reflexive coordinate restriction, which is the identity. A row r in Rows(omega) satisfies omega<=r<=omega, so it equals newRow. Every old-row U, V, nu, I, J, A, B, C, E and F field is obtained by eliminating its impossible inequality r!=newRow.")),
                    Paragraph(Text("A historical birth would have b<omega, omega<=r and max(r,d)=b, contradicting omega<=b. The births field eliminates this contradiction on its exact dependent domain; it supplies no placeholder reservoir, support family or measure. Under CH this actual prefix and predecessor are inputs to SignedOrdinalSuccessor.exists_successor with its original launch and treatment telescope. The initial construction supplies no ordinal schedule, delayed execution, successor F transport, well-founded history, final omega-one limit, CH theorem or official solution."))), DescribeRole.Definition))));
}
