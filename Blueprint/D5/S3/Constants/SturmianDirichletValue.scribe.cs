using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class SturmianDirichletValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Sturmian-Dirichlet value is a fixed affine combination of the golden ratio " +
        "and the twisted cotangent constant.",
        H("Sturmian-Dirichlet Value"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sturmian-dirichlet-value-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/SturmianDirichletValue.sturmian_dirichlet_value_eq"),
                H("The Sturmian-Dirichlet value has its exact golden-ratio form"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("T"), Underscore, Grp(D(0)), Sp, Eq, Sp,
                    Frac,
                    Grp(D(2, 7), Sp, Minus, Sp, D(1, 3), Sqrt, Grp(D(5))),
                    Grp(D(2, 4)), Sp, Eq, Sp,
                    Varphi, Sp, Minus, Sp, Frac, Grp(D(7)), Grp(D(4)),
                    Sp, Plus, Sp, F.Id("C"), Underscore, Grp(Varphi), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Define T0 as (27 - 13 sqrt(5)) / 24 and C_phi as " +
                        "(57 - 25 sqrt(5)) / 24. Mathlib supplies the golden ratio " +
                        "phi = (1 + sqrt(5)) / 2. Substitution and normalization over " +
                        "the reals prove T0 = phi - 7/4 + C_phi exactly.")),
                    Paragraph(Text(
                        "The decimal printed in the source table is an explanatory " +
                        "approximation, not a second exact claim. A checked negative control " +
                        "changes 57 to 58 and proves that the resulting equality fails."))),
                DescribeRole.Theorem
            )),
        []));
}
