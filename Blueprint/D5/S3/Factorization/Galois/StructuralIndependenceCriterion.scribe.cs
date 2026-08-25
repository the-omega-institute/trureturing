using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class StructuralIndependenceCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/StructuralIndependenceCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trivial intersection makes the canonical Galois restriction product bijective.",
        H("Structural Independence Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("structural-independence-criterion"),
            DeclarationHandle.Create(Prefix + "structural_independence_criterion"),
            H("Trivial intersection is structural independence"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The paired restriction homomorphism is constructed from the two "
                        + "normal subextensions. Its kernel is the fixing subgroup of "
                        + "their compositum, so generation of the ambient field makes "
                        + "the map injective.")),
                Paragraph(Text(
                    "Trivial intersection is equivalent to linear disjointness for the "
                        + "finite Galois subextensions. The resulting degree product and "
                        + "the Galois automorphism cardinality formula make the canonical "
                        + "restriction map surjective as well.")),
                Paragraph(Text(
                    "For the contrast clause, a nontrivial proper Galois subextension is "
                        + "paired with the ambient extension. The two fields are distinct, "
                        + "their intersection is the same nontrivial subextension, and "
                        + "linear disjointness fails."))),
            DescribeRole.Theorem))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula MainFormula()
    {
        Formula baseField = F.Id("F");
        Formula ambient = F.Id("E");
        Formula first = F.Id("A");
        Formula second = F.Id("B");
        Formula middle = F.Id("C");
        Formula left = F.Id("L1");
        Formula right = F.Id("L2");
        Formula carrier = Call(F.Id("IntermediateFields"), baseField, ambient);
        Formula bottom = Call(F.Id("Bottom"), baseField, ambient);
        Formula top = Call(F.Id("Top"), baseField, ambient);
        Formula carrierSetup = Seq(
            Call(F.Id("Field"), baseField), Sp, Land, Sp,
            Call(F.Id("Field"), ambient), Sp, Land, Sp,
            Call(F.Id("Algebra"), baseField, ambient), Sp, Land, Sp,
            Call(F.Id("FiniteDimensional"), baseField, ambient));
        Formula extensionSetup = Seq(
            first, Comma, Sp, second, InMacro, Sp, carrier, Sp, Land, Sp,
            Call(F.Id("IsGalois"), baseField, first), Sp, Land, Sp,
            Call(F.Id("IsGalois"), baseField, second), Sp, Land, Sp,
            Call(F.Id("Sup"), first, second), Sp, Eq, Sp, top);
        Formula productClause = Seq(
            Call(F.Id("Inf"), first, second), Sp, Eq, Sp, bottom, Sp,
            Rightarrow, Sp,
            Call(F.Id("Bijective"), Call(F.Id("RestrictionProduct"), first, second)),
            Sp, Land, Sp, Call(F.Id("LinearDisjoint"), first, second));
        Formula contrastClause = Seq(
            Forall, Sp, middle, InMacro, Sp, carrier, Comma, Sp,
            Call(F.Id("IsGalois"), baseField, middle), Sp, Land, Sp,
            middle, Sp, Neq, Sp, bottom, Sp, Land, Sp,
            middle, Sp, Neq, Sp, top, Sp, Rightarrow,
            RowBreak, Grp(), Exists, Sp, left, Comma, Sp, right, InMacro, Sp, carrier,
            Comma, Sp,
            Call(F.Id("IsGalois"), baseField, left), Sp, Land, Sp,
            Call(F.Id("IsGalois"), baseField, right), Sp, Land, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Call(F.Id("Inf"), left, right), Sp, Neq, Sp, bottom, Sp, Land, Sp,
            Neg, Call(F.Id("LinearDisjoint"), left, right));

        return Disp(Seq(
            Forall, Sp, baseField, Comma, Sp, ambient, Comma, Sp,
            carrierSetup, Sp, Rightarrow,
            RowBreak, Grp(), Forall, Sp, extensionSetup, Comma, Sp,
            Open, productClause, Close, Sp, Land,
            RowBreak, Grp(), Open, contrastClause, Close, Dot));
    }
}
