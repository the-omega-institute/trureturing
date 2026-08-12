using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class UnitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden integers are units exactly when their norm is positive or negative one.",
        H("Golden Units"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("norm-of-golden-ratio-powers"),
                DeclarationHandle.Create("D5/S0/Carrier/Units.norm_phi_pow"),
                H("Norm of golden-ratio powers"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("N"), Grp(Varphi, Caret, F.Id("n")), Sp, Eq, Sp,
                    Grp(Minus, D(1)), Caret, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural exponent, multiplicativity of the norm gives the alternating value exactly."))),
                DescribeRole.Theorem),
            Paragraph(
                Ref("D5/S0/Carrier/Units"),
                Text(" proves the exact executable criterion `IsUnit x <-> N(x)=1 or N(x)=-1`. In the forward direction, the multiplicative norm maps units to integer units. In the reverse direction, conjugation gives an explicit inverse, with one sign correction when the norm is negative.")),
            Paragraph(
                Text("The module packages `phi` as a unit with inverse `phi-1`, proves `N(phi^n)=(-1)^n` for natural exponents, and proves that every member of the explicit family `+/-phi^n` is a unit for integral exponents.")))));
}
