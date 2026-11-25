using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class DiagonalLinearCodeCoverageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage.";
    private static readonly LibraryNoteRef Gce = LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal integer-order coverage threshold needs no entanglement.",
        H("An integer order barrier in classical binary linear codes"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-classical-coverage"), DeclarationHandle.Create(Owner + "binary_classical_coverage_iff"),
                H("Universal actual coverage iff integer order"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Gce), Blocks(
                    Paragraph(Text("The state is the uniform diagonal density of a binary linear code. A single nonnegative normalized law on subsets must reproduce the physical GCE hit probabilities of every subsystem. At integer order K, draw K−1 independent uniform linear functionals. They all vanish on a selected subsystem with probability equal to its actual trace moment. Uniform thinning gives the hit law.")),
                    Paragraph(Text("A projective code has one site for each nonzero binary vector. Its full-label Walsh mass is the normalized product of the projective factors. For any noninteger order there is a code for which exactly the last factor is negative. On 1<K<2 this needs only three sites; in the next band a seven-site Fano code gives an exact mass −1/1728 at q=3. The classification is universal, not a claim that all individual codes fail at noninteger K. The noninteger construction here is binary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-fano-readout"), DeclarationHandle.Create(Owner + "physical_fano_readout"),
                H("Actual seven-site Fano full-label mass"), StatementSource.FromAuthor(Fano()),
                AssessedProvenance.FromRepo(Gce), Blocks(
                    Paragraph(Text("The registered observable is the signed full-label bin of the actual complex reduced-state trace table, not the characteristic polynomial substituted by assumption. The positive normalization is 2 to the seventh power."))), DescribeRole.Theorem))));
    private static Formula Bind(FormulaQuantifier q,string n,Formula t,Formula b) =>
        new Formula.Bind(q,FormulaIdentifier.Create(n),t,b);
    private static Formula All(string n,Formula t,Formula b) => Bind(FormulaQuantifier.ForAll,n,t,b);
    private static Formula Statement()
    {
        var k=F.Id("K"); var code=F.Id("C"); var n=F.Id("n");
        var laws=All("C",Call("FiniteBinaryColumnConfigurations"),Call("HitLaw",Call("ActualMomentTable",code,k)));
        var integer=Bind(FormulaQuantifier.Exists,"n",Seq(Mathbb,Grp(F.Id("N"))),Equal(k,Call("Add",n,Num(1))));
        return Disp(All("K",Call("RealsAboveOne"),new Formula.Logic(laws,FormulaLogicOperator.Iff,integer)));
    }
    private static Formula Fano()
    {
        var k=F.Id("K"); var q=Call("Pow",Num(2),Call("Sub",k,Num(1)));
        return Disp(All("K",Call("PositiveReals"),Equal(Call("FullFanoWalshMass",k),
            Call("Div",Call("Product",Call("FanoFactors",q),Num(3)),Num(128)))));
    }
}
