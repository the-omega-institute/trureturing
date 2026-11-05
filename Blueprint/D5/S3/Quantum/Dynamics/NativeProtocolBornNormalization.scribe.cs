using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolBornNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical Born normalization for the complete original sixteen-bit protocol tree.",
        H("Complete native protocols and arbitrary position cuts"),
        Blocks(Describe.Lean(DescribeId.Create("original-complete-born-law"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_complete_born_law"),
            H("The complete original tree has unit total mass and every acquired event has its actual cut trace"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(
                Paragraph(Text("The objects are the original NativeProtocolGraft.Tree, Basis, omega0, gate, callMatrix, projector, Path and mass. Basis consists of all sixteen-bit words at the shifted original positions. The unique fixed root has ones at positions 0, 4 and 8. The proof uses the full matrices at every address in Fin 14, rather than a two-dimensional model supplied as an additional premise.")),
                Paragraph(Text("On each active center-bit pair the actual gate coefficients are a,b,c from the existing calibration calculation. Their existing squared norms, the golden quadratic identity and the actual phase norm give orthogonal unit rows. The remaining control blocks are zero or identity before the phase gate. Reindexing the full carrier by the center-bit involution proves exact energy conservation. Forward calls use this identity and inverse syntax uses nine iterations of the same actual matrix. The original resource counter still charges nine calls; no semantic equality with a separately defined matrix inverse is asserted.")),
                Paragraph(Text("The sum of all terminal squared amplitudes is conserved for every incoming full-carrier vector. Its proof recurses over the original finite tree. Each gate preserves energy, and each selector projector keeps precisely one outcome for every basis word, so the complete outcome sum preserves energy exactly. Each child can have its own feedback addresses, depth and stopping label. Unused outcomes, zero vectors, refusals, failures and early stops remain in the original Path type and its sum. No total-probability, gate-unitarity or projector-completeness certificate is an input.")),
                Paragraph(Text("Applying that conservation to the original normalized computational root gives unit total Born mass, including every final computational result. An acquired event is a Boolean function of the original prefix path, independent of any future report. Positivity of squared amplitudes and domination by the complete sum give its mass between zero and one. Any declared complete prefix is itself such a Tree; the theorem therefore applies at that same common cut.")),
                Paragraph(Text("For any subset I of the sixteen positions, including the empty and full subsets, splitAt is the pinned equivalence restricting a word to I and its complement. The row and complement bases are Boolean functions on those two actual position subtypes. Their dimensions are two to the cardinality of I and two to the cardinality of its complement. cutReduced is the existing right partial trace of the outer product of the same actual branch vector after this coordinate equivalence. eventCut sums those matrices over exactly the acquired histories. The existing partial-trace positivity and trace theorems supply positive semidefiniteness and equality of its complex trace with the real event mass. This reduction is a mathematical marginal and adds no physical record deletion, new register or coherent sum of distinct histories.")),
                Paragraph(Text("This is a partial consequence of V88 definitions 23.1 and 23.2 and the physical trace premise used in theorem 24.1. It does not prove the actual cut determinant lower bound, either minimum-eigenvalue lower bound, a faithful-cut existence statement, or the five-call reference-history and full-record Petz compiler. The arithmetic lower bound for a positive raw event remains the existing original_event_resource_bounds result. The full source atom remains open and uncovered."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e"), I=F.Id("I"), p=F.Id("p"), z=F.Id("z");
        Formula mass=Call("eventMass",T,Call("historyEvent",e));
        Formula cut=Call("eventCut",T,I,e);
        Formula total=FiniteSum(p,Call("Path",T),FiniteSum(z,Call("Basis"),Call("mass",T,p,z)));
        Formula bounds=Conj(Rel(D(0),Leq,mass),Rel(mass,Leq,D(1)));
        Formula law=Conj(Rel(total,Eq,D(1)),bounds,Call("PosSemidef",cut),
            Rel(Call("trace",cut),Eq,Call("complex",mass)));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),
            All("e",Call("Function",Call("Path",T),Call("Bool")),
            All("I",Call("Finset",Call("Fin",D(1,6))),law)))));
    }
    private static Formula FiniteSum(Formula i, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, set), Sp, term);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
}
