using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class UnitGramIndistinguishabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit Gram overlap detects equality and defines an equivalence relation.",
        H("Unit Gram Indistinguishability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-gram-overlap-characterization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PureState/UnitGramIndistinguishability."
                    + "unit_gram_overlap_characterization"),
                H("Unit Gram overlap is exactly record equality"),
                StatementSource.FromAuthor(CharacterizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let e_i be a family of unit vectors in a real or complex inner-product "
                        + "space. The Gram overlap of e_i and e_j is one exactly when the two "
                        + "record vectors are equal.")),
                    Paragraph(Text(
                        "Consequently, declaring two record indices indistinguishable when their "
                        + "Gram overlap is one gives a reflexive, symmetric, and transitive "
                        + "relation. Its classes are precisely the fibers of the record map.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle both returned the exact theorem "
                        + "inner_eq_one_iff_of_norm_eq_one. The Lean proof applies that result "
                        + "directly and only packages equality as an equivalence relation; it "
                        + "does not reprove the equality case of Cauchy-Schwarz."))),
                DescribeRole.Theorem))));

    private static Formula CharacterizationFormula()
    {
        Formula left = Seq(F.Id("e"), Underscore, Grp(F.Id("i")));
        Formula right = Seq(F.Id("e"), Underscore, Grp(F.Id("j")));
        Formula gram = Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
        Formula relation = Seq(Sim, Underscore, Grp(F.Id("G")));

        return Disp(Seq(
            Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
            Vert, Sp, left, Sp, Vert, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Vert, Sp, right, Sp, Vert, Sp, Eq, Sp, D(1), Sp, Rightarrow, RowBreak,
            Open, gram, Sp, Eq, Sp, D(1), Sp, Leftrightarrow, Sp,
            left, Sp, Eq, Sp, right, Close, Sp, Land, RowBreak,
            Operatorname, Grp(F.Id("Equivalence")), Open, relation, Close, Dot));
    }
}
