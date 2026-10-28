using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfQubitCubicCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfQubitCubicCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact endpoint certificate controls the cubic residual on a closed rectangle.",
        H("Closed rectangle estimate for the coupled cubic residual"),
        Blocks(
            Entry("e", "Mean excess",
                "For real t, e(t)=(1-t)^2(2t^2+t+2)/(3(1+t^2)). In the normalization "
                + "X=diag(1,t^2), this is the cubic divided-difference mean minus t.",
                DescribeRole.Definition),
            Entry("beta", "Off-diagonal penalty",
                "Set beta(t)=2(1-t^2)^2(1+3t^2+t^4)/(9(1+t^2)). "
                + "The real denominator is positive for every t.", DescribeRole.Definition),
            Entry("T", "The completed-square term",
                "For real t,y, put T(t,y)=4e(t)ty+e(t)^2y^2.", DescribeRole.Definition),
            Entry("J", "The remaining cubic residual",
                "Set J(t,y)=2(1-2t^2)T(t,y)+beta(t)y^2-(9/4)T(t,y)^2. "
                + "This is the residual obtained after completing the square in the "
                + "trace variable of the two-dimensional coupling estimate.", DescribeRole.Definition),
            Entry("rectangular_J_nonneg", "Nonnegativity on the full closed rectangle",
                "For all real t,y with t>=0, 2t^2<=1, y>=0 and y^2<=2, one has "
                + "J(t,y)>=0. At y=sqrt(2), clearing the positive denominator yields "
                + "a degree-14 Bernstein expansion in q=sqrt(2)t. Its coefficients "
                + "are A+B sqrt(2), with B>=0 and A+(24/17)B>=0. The exact identity "
                + "and all coefficient signs are checked in Lean; no sampled numerical "
                + "premise is used. For the interior of the y interval, J(t,y)=y g(y), "
                + "where g is a cubic with nonpositive quadratic and cubic coefficients. "
                + "An explicit positive factorization of its difference from the endpoint "
                + "chord proves g(y)>=0. Both boundary values t=0 and 2t^2=1, and y=0, "
                + "are included without dividing by y.", DescribeRole.Theorem),
            Paragraph(Text("This is a scalar supplier for the complex Hermitian two-by-two "
                + "cubic coupling estimate studied in connection with the He-Saunderson-Fawzi "
                + "sandwiched Renyi compatibility question, arXiv:2502.05627v1, "
                + "Conjecture 6.2, and DOI 10.1007/s10107-025-02314-0, Conjecture 1. "
                + "It does not settle arbitrary dimension, general base Y, other exponents, "
                + "or the complete HSF conjecture. No literature novelty or official "
                + "acceptance is claimed.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-qubit-cubic-certificate-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
