using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class GreenClassRadiusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first unpinned coordinate determines the sharp prefix-metric radius.",
        H("Sharp Radius of a Finite-Support Agreement Class"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-support-agreement-class-has-a-sharp-radius"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/GreenClassRadius.green_class_radius_sharp"),
                H("The first unpinned coordinate gives the sharp radius"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("O"), Comma, Sp, F.Id("S"), Comma, Sp, F.Id("t"), Comma, Esc,
                    Open, Exists, Sp, F.Id("y"), Comma, Sp,
                    F.Id("y"), Sp, Neq, Sp, F.Id("t"), Open, GammaLower, Open, F.Id("S"), Close, Close,
                    Close, Sp, Rightarrow, Sp,
                    Open,
                    Open, Forall, Sp, F.Id("x"), InMacro,
                    Operatorname, Grp(F.Id("G")), Open, F.Id("S"), Comma, F.Id("t"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("dist")), Open, F.Id("x"), Comma, F.Id("t"), Close,
                    Le, Frac, Grp(D(1)), Grp(D(2)), Caret,
                    Grp(GammaLower, Open, F.Id("S"), Close), Close,
                    Sp, Land, Sp,
                    Open, Exists, Sp, F.Id("x"), InMacro,
                    Operatorname, Grp(F.Id("G")), Open, F.Id("S"), Comma, F.Id("t"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("dist")), Open, F.Id("x"), Comma, F.Id("t"), Close,
                    Eq, Frac, Grp(D(1)), Grp(D(2)), Caret,
                    Grp(GammaLower, Open, F.Id("S"), Close), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite set of coordinates and let G(S,t) contain the sequences "
                        + "that agree with t on S. Mathlib's prefix metric assigns distance "
                        + "(1/2)^k when k is the first coordinate at which two sequences differ. "
                        + "Agreement on S therefore prevents a difference before the least "
                        + "coordinate outside S, giving the stated upper bound.")),
                    Paragraph(Text(
                        "When the alphabet contains a symbol different from t at that first "
                        + "unpinned coordinate, updating t only there produces a member of G(S,t) "
                        + "whose first difference occurs at exactly that coordinate. This witness "
                        + "attains the upper bound, so the radius is sharp.")),
                    Paragraph(Text(
                        "This deposit partially closes only the metric column of source theorem "
                        + "7.4. Its information, measure, layer-spectrum, statistical-independence, "
                        + "and receipt-composition clauses remain unresolved."))),
                DescribeRole.Theorem))));
}
