using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class FixedOutputLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed finite output alphabet of size at least two, escape probability tends to one as the address count grows.",
        H("Fixed-Output Escape Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-output-large-address-escape-probability"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/FixedOutputLimit."
                        + "fixed_output_large_address_escape_probability"),
                H("Fixed-output escape probability tends to one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("Y"),
                    Comma, Sp, D(2), Sp, Leq, Sp, Call("card", F.Id("Y")),
                    Sp, Rightarrow, Sp,
                    Lim, Underscore, Grp(F.Id("A"), Sp, To, Sp, Infty),
                    Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("f")),
                    Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exact escaped-listing cardinality rewrites the uniform escape ratio "
                            + "into the frozen closed form. The existing escape-ratio limit then "
                            + "gives convergence to one for every fixed finite output alphabet "
                            + "with at least two symbols."))),
                DescribeRole.Theorem)),
        []));
}
