using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class RankFourLength28PurityDocument : IScribeDocumentDefinition
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
    private static Formula Hypotheses(bool rankFour)
    {
        var l=Id("lambda");
        var h=new List<Formula> {
            Call("Antitone",l),
            All("i",Call("Fin",N(28)),Le(N(0),Call("lambda",Id("i")))),
            Eq(Call("sum",l),N(1)),
            Call("PosSemidef",Call("K1",Call("boundary",l))),
            Call("PosSemidef",Call("K2",Call("boundary",l))) };
        if(rankFour) h.Add(Le(N(0),Call("L4",l)));
        return And(h.ToArray());
    }
    private static Formula Statement(bool rankFour) => All("lambda",SpectrumType,
        Imp(Hypotheses(rankFour),Le(Call("sumSquares",Id("lambda")),Bound)));
    private static DocumentBlock Desc(string name,string title,Formula statement,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("rank-four-length28-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity."+name),
            H(title),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A length-28 arbitrary-spectrum purity estimate from two rank-three pencils and one rank-four mass inequality.",
        H("Length 28 with rank-four information"),Blocks(
            Desc("L4","Uniform rank-four mass difference",
                All("lambda",SpectrumType,
                    Eq(Call("L4",Id("lambda")),Seq(Call("sumLast",N(10),Id("lambda")),Minus,
                        Call("sumFirst",N(6),Id("lambda"))))),
                "Coordinates are zero-based in Lean. L4 is the sum at indices 18 through 27 minus the sum at indices 0 through 5. The boundary vector is exactly lambda at 0,1,2,22,23,24,25,26,27, and K1 and K2 are the existing QutritSpectralReduction definitions applied to that vector.",DescribeRole.Definition),
            Desc("purity_bound","Arbitrary-spectrum purity estimate",Statement(true),
                "For every antitone real vector lambda of length 28 with all entries nonnegative and total mass one, positivity of both boundary pencils and nonnegativity of L4 imply sumSquares(lambda) <= 1/25. Here sumSquares is the sum of all 28 squared entries. There is no restriction on the number of distinct entries. Let x_i=lambda_i-lambda_(i+1), with x_28=lambda_28 in one-based notation, and let y=(x_2,...,x_27,x_1-2*x_28). The exact rational identity is mass^2/25-purity = y^T P y + x^T H x + sum_(s,i) x_i Tr(B_(s,i) K_s) + L4 w^T x + sum_(a,s) q_a Tr(D_(a,s) K_s) + L4 sum_a gamma_a q_a + sum_s Tr(C_s S_s) + Tr(C_2 T). Both pencil indices are zero-based in this identity. All matrix products use full trace multiplicities, including both off-diagonal entries. P,B,D,C are positive semidefinite by rational LDL factors, while H,w,gamma and the endpoint rank-one weights are entrywise nonnegative. H is not assumed positive semidefinite. The Schur and mixed matrices are defined with v=(1,1,0) and columns of U equal to (1,-1,0),(0,0,1), with no normalization: q_s=v^T K_s v, d_s=U^T K_s U, b_s=U^T K_s v, S_s=q_s d_s-b_s b_s^T and T=q_0 d_1+q_1 d_0-b_0 b_1^T-b_1 b_0^T. DivisionFreeSchur supplies their positivity even for q_s=0. PSD trace pairing and x>=0 then make every summand nonnegative. The single data source is RankFourLength28Data.certificate. The equality spectrum (3,1^27)/30 has purity 1/25 and L4=1/15. This is a spectral relaxation theorem; it does not assert rank-three sufficiency, a literal APPT characterization, physical attainment, or the full APPT conjecture.",DescribeRole.Theorem),
            Desc("claim","The implication with rank-four information omitted",Statement(false),
                "The claim retains arbitrary ordered nonnegative length-28 real spectra, mass one, and both original pencils. It omits only the L4 hypothesis. Its type is literally Prop.",DescribeRole.Definition),
            Desc("result","Both rank-three pencils alone are insufficient",Call("Not",Id("claim")),
                "The spectrum with nine entries 2/37 and nineteen entries 1/37 is ordered, nonnegative and has mass one. Both boundary pencils equal (3I-J)/37 and are positive semidefinite. Its purity is 55/1369 = 1/25 + 6/34225, whereas L4=-2/37. Thus the rank-four hypothesis supplies information needed by the stated spectral implication. The result has the literal type Not claim. It refutes neither APPT nor the APPT purity conjecture.",DescribeRole.Theorem),
            Paragraph(Text("UniformRankFourNecessary proves a fixed rank-four test for arbitrary local dimensions m,n >= 4. Its product corner has six negative and ten positive partial-transpose eigenvectors, with the remaining vectors in the kernel. The actual diagonal APPT hypothesis implies sumFirst 6 <= sumLast 10 without ordering or mass assumptions. At m*n=28 this is exactly L4>=0. No arbitrary-r theorem is supplied. A physical 4 by 7 application requires one sorted diagonal APPT spectrum on which both pencil conditions and L4 are established, as well as an independent attainment construction. An existential spectrum providing only the pencils does not supply that common diagonal APPT hypothesis. Those physical implications are separate from the relaxation proved here.")))));
}
