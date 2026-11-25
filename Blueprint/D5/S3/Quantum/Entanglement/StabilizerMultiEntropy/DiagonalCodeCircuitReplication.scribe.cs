using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class DiagonalCodeCircuitReplicationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication.";
    private static readonly LibraryNoteRef Gce = LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact coverage threshold for diagonal finite-field circuits with arbitrary positive copy counts.",
        H("Actual diagonal circuit coverage and coordinate replication"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-even-circuit-replication"), DeclarationHandle.Create(Owner + "physical_even_fiber_threshold"),
                H("The largest copy count controls an even circuit"), StatementSource.FromAuthor(EvenThreshold()),
                AssessedProvenance.FromRepo(Gce), Blocks(
                    Paragraph(Text("A column circuit is a linearly dependent family whose every proper subfamily is independent. The actual diagonal density is the uniform mixture of evaluations of linear functionals. A diagonal marginal is indexed by a physical subset of tagged copies, while its rank is the rank of the underlying occupied columns. No physical independence of copies is assumed.")),
                    Paragraph(Text("For each original column, sum the signed weights of all nonempty subsets of its copies. This is minus one if the label has any marked copy in that class, and the copy-subset count minus one otherwise. The independent product and the single full-circuit correction are the two surviving terms. Positive rescaling removes the unoccupied fiber factors.")),
                    Paragraph(Text("For even circuit size and nonempty fibers, the worst odd support marks every class except one with the largest copy count. Thus only that maximum enters the exact threshold. For odd unreplicated size at least three the threshold is exactly x at most one half. Omitting a coordinate is not covered by the even theorem's nonempty-fiber hypotheses; the general signed formula still applies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-doubled-four-readout"), DeclarationHandle.Create(Owner + "physical_four_readout"),
                H("Actual doubled four-bit circuit coefficient"), StatementSource.FromAuthor(FourReadout()),
                AssessedProvenance.FromRepo(Gce), Blocks(
                    Paragraph(Text("Use the three standard binary columns and their sum. Duplicate each site, then mark one copy in each of three original classes. The registered observation is the signed Walsh coefficient of the actual eight-site reduced-state trace moments. At x equal to three fifths the original four-site state admits a common classical law while this doubled bin is exactly minus one over 3200."))), DescribeRole.Theorem))));
    private static Formula All(string n,Formula t,Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula EvenThreshold()
    {
        var code=F.Id("C"); var profile=F.Id("J"); var k=F.Id("K");
        var x=Call("Pow",Call("FieldCardinality",code),Call("Sub",Num(1),k));
        var n=Call("CircuitSize",code); var m=Call("MaxCopyCount",profile);
        var left=Call("HitLaw",Call("ActualCopiedCircuitMoments",code,profile,k));
        var right=Call("Le",Call("Pow",x,Call("Sub",n,Num(1))),
            Call("Mul",Call("Pow",Call("Sub",Num(1),x),Call("Sub",n,Num(2))),
                Call("Add",x,Call("Inv",Call("Sub",Call("Pow",Num(2),m),Num(1))))));
        return Disp(All("C",Call("EvenFiniteFieldColumnCircuitsAtLeastFour"),
            All("J",Call("PositiveCopyProfiles",code),
                All("K",Call("RealsAboveOne"),new Formula.Logic(left,FormulaLogicOperator.Iff,right)))));
    }
    private static Formula FourReadout()
    {
        var k=F.Id("K"); var x=Call("Pow",Num(2),Call("Sub",Num(1),k));
        var y=Call("Sub",Num(1),x);
        var num=Call("Sub",Call("Mul",Call("Pow",y,Num(3)),Call("Add",Num(1),Call("Mul",Num(3),x))),
            Call("Mul",Num(3),Call("Pow",x,Num(3)),y));
        return Disp(All("K",Call("PositiveReals"),Equal(Call("ActualDoubledFourWalshMass",k),Call("Div",num,Num(256)))));
    }
}
