using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class CommonWordSensitivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform golden growth of common-word response errors in original source coordinates.",
        H("Common-word source sensitivity"),
        Blocks(
            Paragraph(Text("An original coefficient world W stores r,b,d and the four ordinary coefficients k of one polynomial g(s)=k₀+k₁s+k₂s²+k₃s³. Its source is the existing P=sourceMatrix(r,b)=[[r,b],[r(1-r)/b,1-r]]. The result below holds on the entire OriginalWorld product carrier, and in particular on every original parent world. It includes lower degrees, zero samples, repeated roots and zero drift. No polynomial is fitted to a later window.")),
            Describe.Lean(DescribeId.Create("cubic-common-word-future-product"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CommonWordSensitivity.futureProduct"),
                H("Chronological future product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Boolean word u, futureProduct([])=I and futureProduct(e::u)=futureProduct(u)E(e), where E(true)=J=[[0,1],[1,0]] and E(false)=M=[[0,1],[1,1]]. The head acts first, so the terminal product is Eₙ⋯E₁. The empty future word has product I."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-common-word-clock-eight"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CommonWordSensitivity.clockEight"),
                H("Clock-eight product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("clockEight=M J chronological(6)=[[3,1],[8,3]]. Thus the initial six actions J,M,J,M,M,M are followed by J and M. Future actions multiply on the left of this actual clock-eight product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-common-word-future-read"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CommonWordSensitivity.futureRead"),
                H("Absolute-clock numerical response"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original coefficient world W and every future word u of length n, Y(W,u)=futureRead(W,u)=d+g(8+n)tr(futureProduct(u) clockEight P). The same P, g and d occur at every clock. This is numerical evaluation, with no claim that an additional action or read has been acquired."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-common-word-source-coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CommonWordSensitivity.sourceCoordinates"),
                H("Original eight coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every W, omega(W)=sourceCoordinates(W)=(r,b,r(1-r)/b,d,k₀,k₁,k₂,k₃). Distances use the ordinary maximum norm on these eight coordinates. Write B(W,H) for the condition that every one of the eight coordinate absolute values is at most H. Write script W for OriginalWorld and n(u) for the natural length of u."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cubic-common-word-source-sensitivity"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/CommonWordSensitivity.common_word_source_sensitivity"),
                H("Uniform original-source sensitivity"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let phi=(1+sqrt(5))/2. The displayed theorem quantifies over both original worlds, H and every finite word. H is a common coordinate bound, and the distance is the eight-coordinate source distance. The coefficient 1048576 is a conservative uniform constant.")),
                    Paragraph(Text("For v=(1,phi), each native action has nonnegative entries and sends v below phi v coordinatewise. Induction on chronological words gives sum_j Tᵤ(i,j)vⱼ≤phiⁿvᵢ, while preserving nonnegativity. Since 1≤vᵢ<2, every entry of Tᵤ is at most 2phiⁿ. Multiplication by the fixed clock-eight matrix bounds every advanced entry by 32phiⁿ. The four terms of its trace pairing with a matrix whose entries have absolute value at most H are therefore bounded by 128phiⁿH.")),
                    Paragraph(Text("At the absolute clock 8+n, a cubic with coefficient absolute values bounded by H has absolute value at most 2048H(1+n)³. The same estimate applied to the coefficient difference bounds the gain difference by 2048(1+n)³ times the source distance. Every source-matrix entry is bounded by 2H, including 1-r, and every source-matrix entry difference is bounded by the source distance. Splitting the response difference into drift, gain and source terms gives the displayed inequality. The bound is uniform in the word and its length.")),
                    Paragraph(Text("This result supplies the source-coordinate part of response stability. It does not construct a compact original preimage or prove an inverse Lipschitz estimate from acquired boundary coordinates. In particular the source distance here has not been replaced by the distance between acquired records. The bound makes no claim about execution rights, new observations, physical installation or a universal finite prediction error."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => args.Length switch
    {
        0 => Seq(),
        1 => args[0],
        2 => Seq(args[0], Comma, args[1]),
        _ => throw new System.ArgumentException("At most two arguments are used.")
    };
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Rvert, Sp);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp, Underscore, Grp(Infty));
    private static Formula Statement()
    {
        Formula w = F.Id("W"), z = Seq(w, Apos), h = F.Id("H"), u = F.Id("u");
        Formula n = Call("n", u);
        return Disp(Seq(
            Forall, Sp, w, Comma, z, InMacro, Sp, Mathcal, Grp(w), Comma, Sp,
            Forall, Sp, h, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Open, h, Geq, Sp, D(1), Land, Sp, Call("B", w, h), Land, Sp,
            Call("B", z, h), Close, Implies, Sp,
            Forall, Sp, u, InMacro, Sp, OpenBrace, F.Id("J"), Comma, F.Id("M"), CloseBrace,
            Caret, Grp(Star), Comma, Sp,
            Abs(Seq(Call("Y", w, u), Minus, Call("Y", z, u))), Leq, Sp,
            Open, D(1), Plus, D(1,0,4,8,5,7,6), h, Close,
            Varphi, Caret, Grp(n), Open, D(1), Plus, n, Close, Caret, Grp(D(3)),
            Norm(Seq(Call("omega", w), Minus, Call("omega", z)))));
    }
}
