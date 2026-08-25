using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class SheafPairwiseEqualizerDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer."
            + "sheaf_sections_equiv_pairwise_equalizer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global sections of a type-valued sheaf are exactly compatible local sections.",
        H("Sheaf Pairwise Equalizer"),
        Blocks(Describe.Lean(
            DescribeId.Create("sheaf-pairwise-equalizer"),
            DeclarationHandle.Create(Declaration),
            H("The pairwise restriction equalizer classifies global sections"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A pre-zero hypercover records the cover maps U_i to U. Its canonical "
                        + "pre-one hypercover uses U_i times over U with U_j for every pair, "
                        + "so its section type is the displayed pairwise equalizer.")),
                Paragraph(Text(
                    "The equivalence is required to agree pointwise with the canonical "
                        + "restriction map. Consequently every compatible local family is the "
                        + "restriction of exactly one global section.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the hypercover, pairwise-pullback equalizer, and "
                        + "sheaf-bijectivity lemmas used directly in the proof. Repository "
                        + "search found no existing D5 declaration with both public clauses."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula category = F.Id("C");
        Formula space = F.Id("U");
        Formula cover = F.Id("E");
        Formula presheaf = F.Id("F");
        Formula equivalence = F.Id("e");
        Formula global = F.Id("s");
        Formula compatible = F.Id("a");
        Formula globals = Call("GlobalSections", presheaf, space);
        Formula equalizer = Call("PairwiseOverlapEqualizer", presheaf, cover);
        Formula restriction = Apply(Call("restriction", presheaf, cover), global);

        Formula assumptions = And(
            Call("Category", category),
            And(
                Call("PairwisePullbacks", cover),
                Call("SheafFor", presheaf, cover)));
        Formula computation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("s"), globals)],
            EqualTo(Apply(equivalence, global), restriction));
        Formula uniqueGluing = Seq(
            Forall, Sp, compatible, Colon, Sp, equalizer, Comma, Sp,
            Exists, Bang, Sp, global, Colon, Sp, globals, Comma, Sp,
            restriction, Sp, Eq, Sp, compatible);
        Formula conclusion = Seq(
            Exists, Sp, equivalence, Colon, Sp,
            globals, Sp, Equiv, Sp, equalizer, Comma, Sp,
            Open,
            Open, computation, Close, Sp, Land, Sp,
            Open, uniqueGluing, Close,
            Close);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("C"), type),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("U"), Call("Object", category)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("E"), Call("PreZeroHypercover", space)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("F"), Call("TypePresheaf", category)),
            ],
            Implies(assumptions, conclusion)));
    }
}
