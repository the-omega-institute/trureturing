using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ConceptJoinUniversalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product readout is the universal join of two concept readouts.",
        H("Concept Join Universal Property"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("concept-join-universal-property"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ConceptJoinUniversal.concept_join_universal"),
                H("The product readout is the universal join"),
                StatementSource.FromAuthor(JoinFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joint readout sends x to the pair (q_C x, q_D x). "
                            + "The first two conjuncts factor the component readouts through "
                            + "the product projections.")),
                    Paragraph(Text(
                        "If both component readouts factor through q_E, pairing their factor maps "
                            + "gives the factor map from q_E to the joint readout. This is the "
                            + "universal property of the concept join."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula JoinFormula()
    {
        Formula source = F.Id("X");
        Formula coarse = F.Id("C");
        Formula fine = F.Id("D");
        Formula common = F.Id("E");
        Formula readoutC = Subscript(F.Id("q"), F.Id("C"));
        Formula readoutD = Subscript(F.Id("q"), F.Id("D"));
        Formula readoutE = Subscript(F.Id("q"), F.Id("E"));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula readout(Formula codomain) =>
            Seq(source, Sp, To, Sp, codomain);
        Formula join = Join(readoutC, readoutD);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coarse, Comma, Sp, fine, Comma, Sp,
            common, Colon, Sp, type, Comma, Sp,
            readoutC, Colon, Sp, readout(coarse), Comma, Sp,
            readoutD, Colon, Sp, readout(fine), Comma, Sp,
            readoutE, Colon, Sp, readout(common), Comma, Esc,
            Refines(readoutC, join), Sp, Land, Sp,
            Refines(readoutD, join), Sp, Land, Sp,
            Refines(readoutC, readoutE), Sp, Rightarrow, Sp,
            Refines(readoutD, readoutE), Sp, Rightarrow, Sp,
            Refines(join, readoutE), Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
