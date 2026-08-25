using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.IdealClassGroups;

internal sealed class ClassGroupQuotientUniversalityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/IdealClassGroups/ClassGroupQuotientUniversality."
        + "class_group_quotient_universality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A group homomorphism on invertible fractional ideals that is trivial on every "
            + "principal ideal descends uniquely through the canonical class-group map.",
        H("The Quotient Universal Property of the Ideal Class Group"),
        Blocks(Describe.Lean(
            DescribeId.Create("class-group-quotient-universality"),
            DeclarationHandle.Create(Declaration),
            H("Principal-trivial homomorphisms factor uniquely through ideal classes"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is the group of invertible fractional ideals of a Dedekind "
                        + "domain in its canonical fraction ring. Principal ideals are the "
                        + "image of Mathlib's canonical toPrincipalIdeal homomorphism, and "
                        + "ClassGroup.mk is the displayed quotient projection.")),
                Paragraph(Text(
                    "The hypothesis puts the entire principal-ideal subgroup in the kernel "
                        + "of f. Mathlib's quotient lift then constructs the descended group "
                        + "homomorphism and supplies its computation rule. Surjectivity of the "
                        + "canonical quotient projection forces any second factor to agree on "
                        + "every ideal class, proving the displayed uniqueness.")),
                Paragraph(Text(
                    "This is the quotient universal property itself. It does not choose a "
                        + "generator for a principal ideal and does not replace the class group "
                        + "with an auxiliary quotient. It closes atom generic-residual-18593e23"
                        + "e5f9dbe82590a77864f09745c0c9f00aaedb5e66c2f7b77a428cdd27."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula ring = F.Id("R");
        Formula target = F.Id("H");
        Formula hom = F.Id("f");
        Formula principalUnit = F.Id("x");
        Formula descended = Seq(F.Id("f"), Apos);
        Formula fractionRing = Call("FractionRing", ring);
        Formula fractionalIdealGroup = Call(
            "Units", Call("FractionalIdeal", ring, fractionRing));
        Formula principalIdeal = Call(
            "toPrincipalIdeal", ring, fractionRing, principalUnit);
        Formula classGroup = Call("ClassGroup", ring);
        Formula classMap = Call("ClassGroupMk", ring);

        Formula hypotheses = Seq(
            Call("CommRing", ring), Sp, Land, Sp,
            Call("IsDedekindDomain", ring), Sp, Land, Sp,
            Call("Group", target), Sp, Land, Sp,
            hom, Colon, Sp, Call("GroupHom", fractionalIdealGroup, target), Sp, Land, Sp,
            Open, Forall, Sp, principalUnit, Colon, Sp, Call("Units", fractionRing), Comma, Sp,
            Apply(hom, principalIdeal), Sp, Eq, Sp, D(1), Close);

        Formula factorization = Seq(
            Exists, Bang, Sp, descended, Colon, Sp,
            Call("GroupHom", classGroup, target), Comma, Sp,
            hom, Sp, Eq, Sp, descended, Sp, Circ, Sp, classMap);

        return Disp(Seq(
            Forall, Sp, ring, Comma, Sp, target, Comma, Sp, hom, Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(), factorization, Dot));
    }
}
