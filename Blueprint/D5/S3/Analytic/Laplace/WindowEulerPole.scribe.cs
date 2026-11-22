using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class WindowEulerPoleDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Laplace/WindowEulerPole.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pole of the first-moment Euler forcing obstructs an eventual upper bound on a forward window.",
        H("Euler pole obstruction for forward windows"),
        Blocks(
            Paragraph(Text("Write L for the tail transform of the input g at cutoff U, W for the "
                + "tail transform of its width-h window, Mₕ for the window multiplier, and Q for "
                + "the finite cutoff correction.")),
            Describe.Lean(
                DescribeId.Create("first-moment-euler"),
                DeclarationHandle.Create(Module + "firstMomentEuler"),
                H("First-moment Euler operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The operator sends L to the function z↦zL″(z)+3L′(z)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("no-eventually-le-exp-of-pole"),
                DeclarationHandle.Create(Module + "no_eventually_le_exp_of_pole"),
                H("Peaks forced by a pole"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let h>0. Assume exp(−xt)g(t) is integrable on (U,∞) for every "
                        + "real x>0. Let L(z) be the tail Laplace transform of g from U and assume "
                        + "zL″+3L′=P on Re(z)>0. Suppose P is meromorphic "
                        + "on Re(z)>σ and analytic at each real c with σ<c<0. Assume also that L "
                        + "has a holomorphic extension to a disk about zero agreeing with L on "
                        + "its right half. If P has a pole at a with σ<Re(a)<0, then for every "
                        + "real C the width-h window of g exceeds C exp(σt) at arbitrarily large t.")),
                    Paragraph(Text("An eventual upper bound would give a positive comparison measure. "
                        + "At zero the given extension of L extends W by the window formula. At each "
                        + "negative real cut c, the multiplier is locally nonzero and the Euler image of "
                        + "(W+Q)/Mₕ agrees with P as a meromorphic germ on Re(z)>c by the identity theorem. "
                        + "The Euler equation extends the quotient across c and hence extends W. The convergence theorem "
                        + "makes W holomorphic on Re(z)>σ, and nonvanishing of Mₕ at a makes the quotient "
                        + "holomorphic there. Its Euler image then has a holomorphic germ at a, "
                        + "contrary to the pole of P."))),
                DescribeRole.Theorem))));
}
