using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedKernelCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual critical occupation kernel has a positive leading coefficient and a uniform smaller-order remainder.",
        H("Critical occupation-kernel coefficient estimate"),
        Blocks(
            Paragraph(Text(
                "Let U(m) be the set of permutations of size m avoiding 2413 and 3142, "
                + "and let rho=(sqrt(2)-1)^2. At jump length m>=1 the weight kernelWeight(m-1) "
                + "is rho^m times the cardinality of U(m), with an additional rho/2 at length one only.")),
            Describe.Lean(
                DescribeId.Create("actual-kernel-weight-strict-remainder"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient.actual_kernel_weight_strict_remainder"),
                H("Positive leading term with uniform remainder for lengths at least two"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("C"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("C"), Gt, D(0), Sp, Land, Sp, Open,
                    Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(2), Le, Sp, F.Id("m"), Rightarrow, Sp,
                    Left, Vert, Call("kernelWeight", Seq(F.Id("m"), Minus, D(1))), Minus,
                    Frac, Grp(F.Id("C")), Grp(F.Id("m"), Sqrt, Grp(F.Id("m"))),
                    Right, Vert, Le,
                    Frac, Grp(Frac, Grp(D(2, 1)), Grp(D(1, 6))),
                    Grp(F.Id("m"), Caret, D(2), Sqrt, Grp(F.Id("m"))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The length restriction is a natural-number inequality; powers and square roots in the denominators are real. "
                        + "One constant C works for every admissible length, and the singleton correction is not part of the estimate.")),
                    Paragraph(Text(
                        "The actual cardinality formula makes the normalized generating function quadratic. "
                        + "Its discriminant factors into formal series with linear factors at the critical and rescaled arguments. "
                        + "The constant-one root identifies the coefficients as a convolution of signed central-binomial coefficients "
                        + "with one factor geometrically damped by powers of rho squared. An adjacent-ratio estimate controls the "
                        + "normalized central-binomial profile. Splitting the convolution at half the jump length then bounds both "
                        + "the local coefficient error and the damped tail with the stated uniform constant."))),
                DescribeRole.Theorem))));
}
