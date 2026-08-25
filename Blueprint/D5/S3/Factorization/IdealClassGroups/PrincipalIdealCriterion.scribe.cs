using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.IdealClassGroups;

internal sealed class PrincipalIdealCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/IdealClassGroups/"
        + "PrincipalIdealCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The class map detects principality, while every integer prime count detects ideals.",
        H("Principal Classes and Faithful Prime Counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("principal-ideal-criterion"),
                DeclarationHandle.Create(Prefix + "principal_ideal_criterion"),
                H("The trivial ideal class is exactly the principal locus"),
                StatementSource.FromAuthor(PrincipalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the orientation matching the source statement of Mathlib's "
                        + "ClassGroup.mk_eq_one_iff. No Dedekind-domain assumption is added: "
                        + "the upstream interface requires a domain and a chosen field of "
                        + "fractions."))),
                DescribeRole.Theorem))));

    private static Formula PrincipalFormula()
    {
        Formula ring = F.Id("R");
        Formula field = F.Id("K");
        Formula ideal = F.Id("I");
        Formula assumptions = Seq(
            Call("CommRing", ring), Sp, Land, Sp,
            Call("IsDomain", ring), Sp, Land, Sp,
            Call("Field", field), Sp, Land, Sp,
            Call("Algebra", ring, field), Sp, Land, Sp,
            Call("IsFractionRing", ring, field));
        Formula principal = Call("IsPrincipal", Call("Submodule", ring, field, ideal));
        Formula idealClass = Call("ClassGroupMk", field, ideal);
        return Disp(Seq(
            Forall, Sp, ring, Comma, Sp, field, Comma, Sp, ideal, Comma, RowBreak, Grp(),
            assumptions, Sp, Rightarrow, Sp,
            Open, principal, Sp, Iff, Sp, idealClass, Sp, Eq, Sp, D(1), Close, Dot));
    }

}
