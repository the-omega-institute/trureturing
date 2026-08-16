using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class OrbitStabilizerMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orbit size in a four-element group action is four divided by stabilizer size.",
        H("Orbit-Stabilizer Multiplicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-group-orbits-are-counted-by-stabilizer-size"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/OrbitStabilizerMultiplicity."
                    + "orbit_card_eq_four_div_stabilizer_card"),
                H("Four-group orbit size is four divided by stabilizer size"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("G"), Comma, Sp, F.Id("X"), Comma, Sp,
                    F.Id("x"), Comma, Esc,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("G"), Close,
                    Sp, Eq, Sp, D(4), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("orbit")), Open,
                    F.Id("G"), Comma, Sp, F.Id("x"), Close, Close,
                    Sp, Eq, Sp, D(4), Slash,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("stabilizer")), Open,
                    F.Id("G"), Comma, Sp, F.Id("x"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite group G of cardinality four acting on X, the standard "
                        + "orbit-stabilizer theorem gives card(orbit G x) times "
                        + "card(stabilizer G x) = card(G). The pinned Mathlib theorem "
                        + "MulAction.card_orbit_mul_card_stabilizer_eq_card_group supplies "
                        + "that identity, and nonemptiness of the stabilizer permits exact "
                        + "natural-number division.")),
                    Paragraph(Text(
                        "This closes only the orbit-stabilizer multiplicity clause of appendix "
                        + "E.120. The reported zero counts, symmetry census, and methodological "
                        + "postmortem in the same atom are not asserted."))),
                DescribeRole.Theorem))));
}
