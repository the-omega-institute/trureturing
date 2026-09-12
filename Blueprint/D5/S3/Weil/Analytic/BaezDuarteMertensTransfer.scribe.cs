using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class BaezDuarteMertensTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed unweighted Mertens bound implies power decay of the original finite coefficients.",
        H("BaezDuarteMertensTransfer"),
        Blocks(
            Paragraph(Text("Here c(k) is the existing actual baezDuarte finite binomial coefficient, M(x) is exactly the sum of ArithmeticFunction.moebius(n), cast to the reals, over the natural interval Icc 1 floor(x), and kernel(k,x)=x^(-2)*(1-x^(-2))^k. GlobalM(a) means there exists real A>0 such that for every real x>=1, |M(x)|<=A*Real.rpow(x,a). EventualM(a) means there exist real A>0 and real X such that the same inequality holds for every real x>=X. CoefficientBound(a) means there exists real C>0 such that for every natural k>=1, |c(k)|<=C*Real.rpow(k,a/2-1). No RH hypothesis is assumed by this transfer; the final necessity direction needs the independently verified RH-to-Mertens theorem.")),
            Describe.Lean(
                DescribeId.Create("abel"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_abel_identity"),
                H("The signed Abel identity"),
                StatementSource.FromAuthor(Statement(0)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("For every k>=1, c(k) equals minus the integral over x>1 of M(x)*deriv(kernel(k))(x). The proof uses the public Abel summation theorem with mu(0)=0, retains mu(1)=1, proves local derivative integrability and domination, and proves the boundary term tends to zero. The signed coefficient HasSum identifies the limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("global"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_decay_of_mertens_bound"),
                H("Full quantitative Mertens transfer"),
                StatementSource.FromAuthor(Statement(1)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("For each real a with 0<=a<2, GlobalM(a) implies CoefficientBound(a). With b=1-a/2>0, the two integrable weighted derivative terms contribute A*(B(b,k+1)+k*B(b+1,k)) in real parts. The public beta recurrence and GammaSeq bound give exponent a/2-1 and a constant independent of k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventual"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensTransfer.baez_duarte_decay_of_eventual_mertens_bound"),
                H("The actual finite prefix is absorbed"),
                StatementSource.FromAuthor(Statement(2)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The eventual bound extends to x>=1 using the actual finite sum: |M(x)|<=floor(x)<=x and x^a>=1. The constant max(A,max(1,X)) retains every prefix term, including n=1. The resulting bound is then passed to the quantitative transfer."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement(int index)
    {
        Formula a = FormulaDsl.Id("a"), b = FormulaDsl.Id("b"), k = FormulaDsl.Id("k");
        Formula x = FormulaDsl.Id("x"), C = FormulaDsl.Id("C");
        return Disp(index switch
        {
            0 => Seq(k, Ge, Sp, D(1), Rightarrow, Sp, Call("c", k), Eq, Minus, Call("integralIoi", D(1), Call("MtimesDerivative", k))),
            1 => Seq(D(0), Le, Sp, a, Land, Sp, a, Lt, D(2), Land, Sp, Call("GlobalM", a), Rightarrow, Sp, Call("CoefficientBound", a)),
            2 => Seq(D(0), Le, Sp, a, Land, Sp, a, Lt, D(2), Land, Sp, Call("EventualM", a), Rightarrow, Sp, Call("CoefficientBound", a)),
            _ => throw new System.ArgumentOutOfRangeException(nameof(index)),
        });
    }
}
