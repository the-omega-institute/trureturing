using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class SymmetryBreakingSourceClassificationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Attribution/SymmetryBreakingSourceClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed symmetry obstructs equivariant selection, and the declared source taxonomy "
            + "has four exhaustive classes.",
        H("Fixed Symmetry and Its Declared Breaking Sources"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-symmetry-and-source-classification"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "fixed_symmetry_obstruction_and_source_classification"),
                H("Fixed symmetry obstructs selection and sources have a declared class"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The selector obstruction is inherited directly from the existing "
                            + "common-fixed-symmetry theorem. A nonempty set of source tags "
                            + "then supplies a tag, and constructor elimination places it in "
                            + "one of the four declared classes.")),
                    Paragraph(Text(
                        "The source type is a closed formal taxonomy. This statement does not "
                            + "claim that an unmodeled real-world mechanism has already been "
                            + "mapped into that taxonomy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-fixed-symmetry-premise-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "common_fixed_symmetry_hypothesis_is_necessary"),
                H("The common fixed-symmetry premise is necessary"),
                StatementSource.FromAuthor(FixedSymmetryNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On singleton state and action spaces, the constant selector is admissible "
                        + "and equivariant for the trivial action. Every action is fixed, so the "
                        + "fixed-point-free symmetry premise is false."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nonempty-source-premise-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "nonempty_source_hypothesis_is_necessary"),
                H("A source set must be nonempty"),
                StatementSource.FromAuthor(NonemptyNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty source set contains no tag, hence it cannot witness any of the "
                        + "four declared source classes."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("empty-state-has-no-fixed-symmetry-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "empty_state_cannot_supply_fixed_symmetry_witness"),
                H("An empty state space supplies no obstruction witness"),
                StatementSource.FromAuthor(EmptyStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The obstruction starts with a state. The empty type has no inhabitant, "
                        + "so this degenerate state space cannot satisfy that premise."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("singleton-source-is-classified"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "singleton_source_is_classified"),
                H("A singleton internal source is classified"),
                StatementSource.FromAuthor(SingletonSourceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The singleton containing the observer-internal source tag gives a concrete "
                        + "nonempty classification witness."))),
                DescribeRole.Lemma))));

    private static Formula Listed(Formula source) =>
        Call("IsDeclaredSymmetryBreakingSource", source);

    private static Formula MainFormula()
    {
        Formula admissible = F.Id("admissible");
        Formula sources = F.Id("sources");
        Formula source = F.Id("source");

        return Disp(Seq(
            Call("FixedSymmetry", admissible), Sp, Land, Sp,
            Call("Nonempty", sources), Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Call("ExistsAdmissibleEquivariantSelector", admissible), Sp,
            Land, Sp, Exists, Sp, source, Sp, InMacro, Sp, sources, Comma, Sp,
            Listed(source), Dot));
    }

    private static Formula FixedSymmetryNecessaryFormula()
    {
        Formula unit = F.Id("Unit");

        return Disp(Seq(
            Call("ExistsAdmissibleEquivariantSelector", unit, unit), Sp, Land, Sp,
            Neg, Sp, Call("FixedPointFreeSymmetry", unit, unit), Dot));
    }

    private static Formula NonemptyNecessaryFormula()
    {
        Formula source = F.Id("source");

        return Disp(Seq(
            Neg, Sp, Exists, Sp, source, Sp, InMacro, Sp,
            Call("emptySet", F.Id("SymmetryBreakingSource")), Comma, Sp,
            Listed(source), Dot));
    }

    private static Formula EmptyStateFormula() =>
        Disp(Seq(Neg, Sp, Call("Nonempty", F.Id("Empty")), Dot));

    private static Formula SingletonSourceFormula()
    {
        Formula source = F.Id("source");
        Formula singleton = Call("singleton", F.Id("observerInternal"));

        return Disp(Seq(
            Exists, Sp, source, Sp, InMacro, Sp, singleton, Comma, Sp,
            Listed(source), Dot));
    }
}
