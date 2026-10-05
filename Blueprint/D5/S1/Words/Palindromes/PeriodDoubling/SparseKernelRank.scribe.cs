using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;
internal sealed class SparseKernelRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinite rational rank of the PPL binary kernel.",H("Sparse Kernel Rank"),Blocks(
        Describe.Lean(DescribeId.Create("pd-sparsekernelrank-stronger-ppl-kernel-span"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.stronger_PPL_kernel_span"),
            H("Infinite rational kernel span"),StatementSource.FromAuthor(Disp(SpanFormula())),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational span of the binary kernel of period-doubling prefix palindromic length is infinite-dimensional. Evaluating the subsequences at the sparse upper blocks gives a matrix which becomes unit lower triangular after subtracting two separable terms. The evaluation size is arbitrary. The exact diagonal and off-diagonal values supply its entries. cast denotes natural-to-rational coercion."))),DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);

    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);




    private static Formula SpanFormula()
    {
        var value=Cast(Call("PL",Call("ofFn",Seq(LambdaLower,Sp,V("i"),Colon,Call("Fin",V("n")),Sp,Mapsto,Sp,Upd(Call("val",V("i")))))),Q());
        var p=Seq(LambdaLower,Sp,V("n"),Colon,N(),Sp,Mapsto,Sp,value);
        return NotF(Call("FiniteDimensional",Q(),Call("span",Q(),Call("twoKernel",p))));
    }
}
