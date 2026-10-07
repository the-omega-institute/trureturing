using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class TwistedPeriodicHistoriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("H", I("Type")), B("group", Call("Group", I("H"))),
         B("finiteH", Call("Fintype", I("H"))), B("n", I("Nat")),
         B("C", Call("GroupMat", I("H"), I("n"), I("n"))), B("h", I("H")),
         B("j", I("Nat")), B("hj", Call("NatPositive", I("j")))], body);
    private static Formula Period => Call("TwistedPeriod", I("C"), I("h"), I("j"));
    private static Formula Words => Call("SeamWords", I("C"), I("h"), I("hj"));
    private static Formula Count => Call("sumFin", I("n"), I("i"),
        Call("sumGroup", I("H"), I("z"),
            Call("coeff", Call("entry", Call("matrixPower", I("C"), I("j")), I("i"), I("i")),
                Call("product", Call("product", Call("inverse", I("z")), I("h")), I("z")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive twisted period is an actual legal bilateral history reconstructed from one finite numbered word and its ordered group seam.",
        H("Twisted periods from finite seamed words"),
        Blocks(
            Describe.Lean(DescribeId.Create("twisted-period-equivalence"),
                DeclarationHandle.Create(Prefix + "twistedPeriodEquiv"),
                H("Restriction and signed extension are inverse"),
                StatementSource.FromAuthor(Disp(All(Call("Equiv", Period, Words)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("NatPositive(j) means 0<j. TwistedPeriod(C,h,j) is the subtype of actual History(expandedGraph C) satisfying shift iterated j times of x equals groupHistory(C,h,x). SeamWords(C,h,hj) is Sigma i:Fin n, Sigma z:H, WordFiber C hj i i (z inverse times h times z). WordFiber retains every original edge and parallel-edge number, both endpoints and the ordered total label. The bridge requires no essentiality, inertness, assumed history equivalence or assumed finiteness of histories. The zero-vertex case is included naturally as an empty sigma; no period-zero assertion is made.")),
                    Paragraph(Text("Restriction reads the actual length-j window at zero and its initial coordinate z. The original expandedWordCoordinates inverse recovers this window as liftWord(w,z). Last-edge legality and the twist at zero give equal base endpoints and z*totalLabel(w)=h*z, hence totalLabel(w)=z inverse*h*z in this order.")),
                    Paragraph(Text("For every integer address t=assemble j(q,r), extension uses the exact numbered edge (w.edge r, h^q*(z*prefixLabel w r)). Internal legality is supplied by liftWord. At each seam, the original lift_source and lift_target endpoint equations and z*totalLabel(w)=h*z join adjacent blocks. Euclidean blockAddress and both assemble inverse identities cover all negative as well as positive positions. The twist is proved on every integer coordinate. Signed recovery of an arbitrary twisted history uses the commuting translation and left-group permutations, Function.IsFixedPt.perm_zpow and Commute.mul_zpow. Thus restriction followed by extension recovers every coordinate, and extension followed by restriction recovers the same dependent finite word data. No generic signed-action induction or duplicated finite-word coordinate proof is added."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("twisted-period-fintype"),
                DeclarationHandle.Create(Prefix + "twistedPeriodFintype"),
                H("Actual finite enumeration"),
                StatementSource.FromAuthor(Disp(All(Call("Fintype", Period)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive-length argument is supplied explicitly. Fintype.ofEquiv transports the finite dependent sigma enumeration through twistedPeriodEquiv inverse. Consequently the actual twisted-history subtype is Finite. No global finiteness instance for unrestricted History is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("twisted-period-cardinality"),
                DeclarationHandle.Create(Prefix + "twistedPeriod_card"),
                H("Exact diagonal conjugacy sum"),
                StatementSource.FromAuthor(Disp(All(Equal(Call("FintypeCard", Period), Count)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FintypeCard uses the constructed twistedPeriodFintype. sumFin and sumGroup sum over every i:Fin n and z:H. MatrixPower is the same natural group-ring matrix power C^j. The proof uses the actual reconstruction equivalence on its live path, expands the two sigma cardinalities and directly applies FixedBlockRigidity.wordFiber_card to each loop fiber. It counts actual bilateral histories, including parallel edges, rather than substituting a coefficient-only proxy. This supplies the bridge for the original18.4 example; the literal D8 coefficients, period-one cancellation, all positive counts16^j and arbitrary original coprime block-map iterate laws remain separate obligations."))),
                DescribeRole.Theorem))));
}
