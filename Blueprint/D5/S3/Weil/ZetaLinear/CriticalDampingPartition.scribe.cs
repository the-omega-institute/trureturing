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
            StatementSource.FromAuthor(CertificateFormula()),
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

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CertificateFormula()
    {
        Formula d = F.Id("d");
        Formula tau = F.Id("tau");
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));
        Formula partition = Call("dampingPartition", d, tau);
        Formula defect = Call("criticalDampingPartitionDefect", d, tau);
        Formula centered = Call("centeredDampingOperator", d, half);
        Formula minusTau = Seq(Open, Minus, tau, Close);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp, tau, Colon, Sp,
            Call("CenteredSpectrumSymmetric", d, half), Sp, Land, Sp,
            tau, Sp, Neq, Sp, D(0), Sp, Rightarrow,
            RowBreak, Grp(),
            partition, Sp, Eq, Sp,
            Exp, Open, Seq(Frac, Grp(tau), Grp(D(2))), Close, Sp, Cdot, Sp,
            Call("tr", Exp, Open, minusTau, Sp, Cdot, Sp,
                Call("dampingOperator", d), Close), Sp, Land,
            RowBreak, Grp(),
            partition, Sp, Eq, Sp,
            Call("tr", Exp, Open, minusTau, Sp, Cdot, Sp, centered, Close),
            Sp, Land, Sp,
            partition, Sp, Eq, Sp,
            Call("tr", Call("cosh", Seq(tau, Sp, Cdot, Sp, centered))),
            Sp, Land,
            RowBreak, Grp(),
            D(0), Sp, Leq, Sp, defect, Sp, Land, Sp,
            Open, Open, Forall, Sp, F.Id("i"), Comma, Sp,
            new Formula.Subscript(F.Id("d"), F.Id("i")), Sp, Eq, Sp, half,
            Close, Sp, Iff, Sp, defect, Sp, Eq, Sp, D(0), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

}
