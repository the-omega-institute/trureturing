using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Probability;

internal sealed class GeneralEquivariantEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula f = F.Id("f");
        Formula i = F.Id("i");
        Formula y = F.Id("Y");
        Formula orbitSet = Call("Orb", F.Id("A"));
        Formula omega = Seq(F.Id("omega"), Underscore, i);
        Formula totalFactor = Seq(Call("card", y), Caret, Grp(omega));
        Formula fixedCount = Call("card", Call("Fix", f));
        Formula escapedFactor = Seq(
            Open, totalFactor, Sp, Minus, Sp, fixedCount, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform equivariant escape probability factors over every address orbit.",
            H("General Equivariant Escape Probability"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("general-equivariant-escape-probability"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/Probability/GeneralEquivariantEscape."
                        + "general_equivariant_escape_probability"),
                    H("General equivariant escape probability"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("PescEq", f), Sp, Eq, Sp,
                        Frac,
                        Grp(Prod, Underscore,
                            Grp(i, Sp, InMacro, Sp, orbitSet), Sp, escapedFactor),
                        Grp(Prod, Underscore,
                            Grp(i, Sp, InMacro, Sp, orbitSet), Sp, totalFactor),
                        Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let i range over the G-orbits of addresses. The supplied orbit "
                            + "decomposition identifies equivariant listings with diagonal and "
                            + "stabilizer-orbit row parameters while preserving the escape "
                            + "predicate. If omega_i is the number of stabilizer orbits, n is "
                            + "the cardinality of Y, and k is the number of fixed points of f, "
                            + "then orbit i contributes n^omega_i total choices and "
                            + "n^omega_i-k escaping choices.")),
                        Paragraph(Text(
                            "The imported orbit-product count gives the numerator. Counting the "
                            + "same public parameter equivalence gives the denominator, and the "
                            + "pinned uniform-PMF theorem converts their cardinality ratio into "
                            + "the displayed outer-measure probability.")),
                        Paragraph(Text(
                            "Repository searches found only the transitive probability theorem. "
                            + "Pinned Mathlib supplies PMF.toOuterMeasure_uniformOfFintype_apply, "
                            + "Fintype.card_pi, and the finite product arithmetic, but no packaged "
                            + "equivariant orbit-decomposition probability formula."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("transitive-probability-is-a-general-corollary"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/Probability/GeneralEquivariantEscape."
                        + "transitive_equivariant_escape_probability_from_general"),
                    H("The transitive formula is a corollary"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("PescEq", f), Sp, Eq, Sp, D(1), Sp, Minus, Sp,
                        Frac,
                        Grp(fixedCount),
                        Grp(Call("card", y), Caret, Grp(omega)),
                        Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For a transitive action the orbit index is a singleton. Applying "
                            + "the general theorem collapses both finite products to the factor "
                            + "at any chosen orbit representative i, after which the denominator "
                            + "is nonzero and the ratio is 1-k/n^omega_i. Thus the frozen "
                            + "transitive formula is obtained as a specialization rather than "
                            + "reproved by a separate counting argument."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Diagonal/Probability/EquivariantEscape")),
            ]));
    }
}
