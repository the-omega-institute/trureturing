using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class CriticalDampingPartitionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/CriticalDampingPartition."
            + "critical_damping_partition_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite reflection-symmetric damping spectrum has equivalent diagonal, "
            + "centered-exponential, and hyperbolic-cosine partition traces, with a "
            + "nonnegative defect that vanishes precisely on the critical line.",
        H("Critical Damping Partition"),
        Blocks(Describe.Lean(
            DescribeId.Create("critical-damping-partition-certificate"),
            DeclarationHandle.Create(Declaration),
            H("The centered damping partition has a nonnegative critical defect"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                F.Id("d"), Colon, Sp,
                Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close,
                Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                Tau, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                Operatorname, Grp(F.Id("CenteredSpectrumSymmetric")),
                Open, F.Id("d"), Comma, Sp, Frac, Grp(D(1)), Grp(D(2)), Close,
                Sp, Land, Sp, Tau, Neq, D(0), Sp, Rightarrow, Esc,
                Open,
                Operatorname, Grp(F.Id("dampingPartition")),
                Open, F.Id("d"), Comma, Sp, Tau, Close,
                Eq, Exp, Open, Frac, Grp(Tau), Grp(D(2)), Close, Sp, Cdot, Sp,
                Operatorname, Grp(F.Id("tr")), Open,
                Exp, Open, Minus, Tau, Sp, Cdot, Sp,
                Operatorname, Grp(F.Id("dampingOperator")), Open, F.Id("d"), Close,
                Close, Close, Sp, Land, Esc,
                Operatorname, Grp(F.Id("dampingPartition")),
                Open, F.Id("d"), Comma, Sp, Tau, Close,
                Eq, Operatorname, Grp(F.Id("tr")), Open,
                Exp, Open, Minus, Tau, Sp, Cdot, Sp,
                Operatorname, Grp(F.Id("centeredDampingOperator")),
                Open, F.Id("d"), Comma, Sp, Frac, Grp(D(1)), Grp(D(2)), Close,
                Close, Close, Sp, Land, Esc,
                Operatorname, Grp(F.Id("dampingPartition")),
                Open, F.Id("d"), Comma, Sp, Tau, Close,
                Eq, Operatorname, Grp(F.Id("tr")), Open,
                Operatorname, Grp(F.Id("matrixCosh")), Open,
                Tau, Sp, Cdot, Sp,
                Operatorname, Grp(F.Id("centeredDampingOperator")),
                Open, F.Id("d"), Comma, Sp, Frac, Grp(D(1)), Grp(D(2)), Close,
                Close, Close, Sp, Land, Esc,
                D(0), Leq, Operatorname, Grp(F.Id("criticalDampingPartitionDefect")),
                Open, F.Id("d"), Comma, Sp, Tau, Close, Sp, Land, Esc,
                Open, Open, Forall, Sp, F.Id("i"), InMacro,
                Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, Comma, Sp,
                F.Id("d"), Open, F.Id("i"), Close,
                Eq, Frac, Grp(D(1)), Grp(D(2)), Close,
                Sp, Leftrightarrow, Sp,
                Operatorname, Grp(F.Id("criticalDampingPartitionDefect")),
                Open, F.Id("d"), Comma, Sp, Tau, Close, Eq, D(0),
                Close,
                Close))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite family of real damping rates defines a complex diagonal "
                        + "matrix. Subtracting one half times the identity produces the "
                        + "centered damping operator, while the normalized partition "
                        + "function is the exponential prefactor times the finite heat "
                        + "sum.")),
                Paragraph(Text(
                    "The reflection hypothesis is witnessed by a permutation that negates "
                        + "every centered rate. It cancels the odd exponential contribution "
                        + "and identifies the partition with the trace of the matrix "
                        + "hyperbolic cosine.")),
                Paragraph(Text(
                    "The resulting partition defect is a finite sum of cosh(x)-1 terms and "
                        + "is nonnegative. At every nonzero scale it vanishes exactly when "
                        + "all damping rates equal one half. The same module proves the "
                        + "finite maximum norm formula and explicit critical and off-line "
                        + "three-point witnesses."))),
            DescribeRole.Theorem))));
}
