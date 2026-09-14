using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class BaezDuarteMertensKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original inverse-square kernel has a corrected beta integral and a uniform power bound.",
        H("BaezDuarteMertensKernel"),
        Blocks(
            Paragraph(Text("Write B(u,v) for the public Complex.betaIntegral. For real x>=1 set kernel(k,x)=x^(-2)*(1-x^(-2))^k. The derivative in the formulas is -2*x^(-3)*(1-x^(-2))^k+2*k*x^(-5)*(1-x^(-2))^(k-1). Real powers use Real.rpow; k is natural. Every beta estimate quantifies one positive real C before all k>=1, so its constant is independent of k. Write weightedKernel(b,k)(x)=x^(-2*b-1)*(1-x^(-2))^k. The kernel integrals and their integrability are proved for every natural k, including zero, and every real b>0.")),
            Describe.Lean(
                DescribeId.Create("beta-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_beta_bound"),
                H("Uniform beta power bound"),
                StatementSource.FromAuthor(Statement(0)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The public GammaSeq identity and convergence bound the entire positive-index beta sequence. This directly reuses the existing Euler limit, with no new Gamma asymptotic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("derivative"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_hasDerivAt"),
                H("Correctly indexed derivative"),
                StatementSource.FromAuthor(Statement(1)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("For k>=1 and x>=1 the stated derivative is a HasDerivAt certificate of the actual original kernel. The negative first term and k-1 exponent are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integrability"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_integrable"),
                H("Integrability of the transformed kernel"),
                StatementSource.FromAuthor(Statement(2)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The inverse-square substitution maps x>1 to 0<y<1. The injective Jacobian theorem transports beta integrability; an integral value alone is never used as integrability evidence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_kernel_integral"),
                H("The beta integral with its half factor"),
                StatementSource.FromAuthor(Statement(3)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("Here weightedKernel(b,k)(x)=x^(-2*b-1)*(1-x^(-2))^k. Its integral over x>1 is the real part of B(b,k+1) divided by two. This proves the factor missing in the printed square substitution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("combined"),
                DeclarationHandle.Create("D5/S3/Weil/Analytic/BaezDuarteMertensKernel.baez_duarte_beta_combined_bound"),
                H("A common bound for both derivative terms"),
                StatementSource.FromAuthor(Statement(4)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion")),
                Blocks(Paragraph(Text("The public beta recurrence identifies the sum of the two real beta terms with (1+b)*Re(B(b,k+1)). The preceding uniform bound supplies a single positive C for the full positive-index sequence."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement(int index)
    {
        Formula a = FormulaDsl.Id("a"), b = FormulaDsl.Id("b"), k = FormulaDsl.Id("k");
        Formula x = FormulaDsl.Id("x"), C = FormulaDsl.Id("C");
        return Disp(index switch
        {
            0 => Seq(b, Gt, D(0), Rightarrow, Sp, Exists, Sp, C, Gt, D(0), Comma, Sp, Forall, Sp, k, Ge, Sp, D(1), Comma, Sp, Call("norm", Call("B", b, Seq(k, Plus, D(1)))), Le, Sp, C, Sp, Call("rpow", k, Seq(Minus, b))),
            1 => Seq(k, Ge, Sp, D(1), Land, Sp, x, Ge, Sp, D(1), Rightarrow, Sp, Call("HasDerivAt", Call("kernel", k), Call("kernelDerivative", k, x), x)),
            2 => Seq(b, Gt, D(0), Rightarrow, Sp, Call("IntegrableOn", Call("weightedKernel", b, k), Call("Ioi", D(1)))),
            3 => Seq(b, Gt, D(0), Rightarrow, Sp, Call("integralIoi", D(1), Call("weightedKernel", b, k)), Eq, new Formula.Fraction(Call("Re", Call("B", b, Seq(k, Plus, D(1)))), D(2))),
            4 => Seq(b, Gt, D(0), Rightarrow, Sp, Exists, Sp, C, Gt, D(0), Comma, Sp, Forall, Sp, k, Ge, Sp, D(1), Comma, Sp, Call("Re", Call("B", b, Seq(k, Plus, D(1)))), Plus, k, Sp, Call("Re", Call("B", Seq(b, Plus, D(1)), k)), Le, Sp, C, Sp, Call("rpow", k, Seq(Minus, b))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(index)),
        });
    }
}
