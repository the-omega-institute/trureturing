using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CotangentHeckeIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial closure of theorem 5.10: the cotangent double-angle identity.",
        H("Cotangent Hecke Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cotangent-double-angle"),
                DeclarationHandle.Create("D5/S3/Fourier/CotangentHeckeIdentity.cotangent_double_angle"),
                H("The cotangent double-angle identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("theta"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    Sp, Operatorname, Grp(F.Id("cot")), Open, F.Id("theta"), Close, Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("cot")), Open, F.Id("theta"), Plus, Frac, Grp(F.Id("pi")), Grp(D(2)), Close,
                    Sp, Eq, Sp, D(2), Sp, Operatorname, Grp(F.Id("cot")), Open, D(2), F.Id("theta"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the first, self-contained clause of the source theorem. The regularized-function equations, four corollaries, numerical certificates, and the later correction remain unresolved and are intentionally excluded from this partial closure."))),
                DescribeRole.Theorem
            ))));
}
