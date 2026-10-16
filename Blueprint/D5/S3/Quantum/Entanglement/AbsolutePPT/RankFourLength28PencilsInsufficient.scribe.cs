using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class RankFourLength28PencilsInsufficientDocument : IScribeDocumentDefinition
{
    private static Formula Id(string name) => F.Id(name);
    private static Formula N(int n) => Num(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula And(params Formula[] args) =>
        Seq(args.SelectMany((a,i) => i == 0 ? new[] {Par(a)} : new[] {Land, Sp, Par(a)}).ToArray());
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Rightarrow, Sp, b);
    private static Formula Bound => new Formula.Fraction(N(1),N(25));
    private static Formula SpectrumType => Seq(Call("Fin",N(28)), Rightarrow, Mathbb, Grp(Id("R")));
    private static Formula Hypotheses()
    {
        var l=Id("lambda");
        var h=new List<Formula> {
            Call("Antitone",l),
            All("i",Call("Fin",N(28)),Le(N(0),Call("lambda",Id("i")))),
            Eq(Call("sum",l),N(1)),
            Call("PosSemidef",Call("K1",Call("boundary",l))),
            Call("PosSemidef",Call("K2",Call("boundary",l))) };
        return And(h.ToArray());
    }
    private static Formula Statement() => All("lambda",SpectrumType,
        Imp(Hypotheses(),Le(Call("sumSquares",Id("lambda")),Bound)));
    private static DocumentBlock Desc(string name,string title,Formula statement,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("rank-four-length28-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient."+name),
            H(title),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit counterexample to the length-28 purity implication with only two rank-three pencils.",
        H("Two boundary pencils are insufficient"),Blocks(
            Desc("claim","The implication with rank-four information omitted",Statement(),
                "The claim retains arbitrary ordered nonnegative length-28 real spectra, mass one, and both original pencils. It omits only the L4 hypothesis. Its type is literally Prop.",DescribeRole.Definition),
            Desc("result","Both rank-three pencils alone are insufficient",Call("Not",Id("claim")),
                "The spectrum with nine entries 2/37 and nineteen entries 1/37 is ordered, nonnegative and has mass one. Both boundary pencils equal (3I-J)/37 and are positive semidefinite. Its purity is 55/1369 = 1/25 + 6/34225, whereas L4=-2/37. Thus the rank-four hypothesis supplies information needed by the stated spectral implication. The result has the literal type Not claim. It refutes neither APPT nor the APPT purity conjecture.",DescribeRole.Theorem))));
}
