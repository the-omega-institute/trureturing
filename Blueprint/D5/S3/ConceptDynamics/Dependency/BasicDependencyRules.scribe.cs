using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dependency;

internal sealed class BasicDependencyRulesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula typeA = F.Id("A");
        Formula typeB = F.Id("B");
        Formula typeC = F.Id("C");
        Formula typeD = F.Id("D");
        Formula readoutA = new Formula.Subscript(F.Id("q"), typeA);
        Formula readoutB = new Formula.Subscript(F.Id("q"), typeB);
        Formula readoutC = new Formula.Subscript(F.Id("q"), typeC);
        Formula readoutD = new Formula.Subscript(F.Id("q"), typeD);
        Formula joinAB = Call("conceptJoin", readoutA, readoutB);
        Formula joinBC = Call("conceptJoin", readoutB, readoutC);
        Formula joinAC = Call("conceptJoin", readoutA, readoutC);
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula arrow = To;

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            state, Comma, Sp, typeA, Comma, Sp, typeB, Comma, Sp,
            typeC, Comma, Sp, typeD, Colon, Sp, universe, Comma,
            RowBreak, Grp(),
            readoutA, Colon, Sp, state, Sp, arrow, Sp, typeA, Comma, Sp,
            readoutB, Colon, Sp, state, Sp, arrow, Sp, typeB, Comma,
            RowBreak, Grp(),
            readoutC, Colon, Sp, state, Sp, arrow, Sp, typeC, Comma, Sp,
            readoutD, Colon, Sp, state, Sp, arrow, Sp, typeD, Comma,
            RowBreak, Grp(),
            Call("Refines", readoutA, readoutA), Sp, Land,
            RowBreak, Grp(),
            Open,
            Call("Refines", readoutA, joinAB), Sp, Land, Sp,
            Call("Refines", readoutB, joinAB),
            Close, Sp, Land,
            RowBreak, Grp(),
            Open,
            Call("Refines", readoutB, readoutA), Sp, Land, Sp,
            Call("Refines", readoutC, readoutB),
            Close, Sp, Rightarrow, Sp,
            Call("Refines", readoutC, readoutA), Sp, Land,
            RowBreak, Grp(),
            Open,
            Call("Refines", readoutB, readoutA), Sp, Rightarrow, Sp,
            Call("Refines", joinBC, joinAC),
            Close, Sp, Land,
            RowBreak, Grp(),
            Open,
            Call("Refines", readoutB, readoutA), Sp, Land, Sp,
            Call("Refines", readoutC, readoutA),
            Close, Sp, Rightarrow, Sp,
            Call("Refines", joinBC, readoutA), Sp, Land,
            RowBreak, Grp(),
            Call("Refines", joinBC, readoutA), Sp, Rightarrow, Sp,
            Open,
            Call("Refines", readoutB, readoutA), Sp, Land, Sp,
            Call("Refines", readoutC, readoutA),
            Close, Sp, Land,
            RowBreak, Grp(),
            Open,
            Call("Refines", readoutB, readoutA), Sp, Land, Sp,
            Call("Refines", readoutD, joinBC),
            Close, Sp, Rightarrow, Sp,
            Call("Refines", readoutD, joinAC), Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Factorization dependence is closed under identity, composition, and joint readouts.",
            H("Basic Dependency Rules"),
            Blocks(Describe.Lean(
                DescribeId.Create("concept-dependence-obeys-the-basic-rules"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Dependency/BasicDependencyRules."
                        + "basic_dependency_rules"),
                H("Concept dependence obeys the basic rules"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Identity and composition of factor maps give reflexivity and transitivity. "
                        + "Product projections, paired factor maps, and preservation of a shared "
                        + "coordinate give projection, augmentation, merge, decomposition, and "
                        + "pseudotransitivity."))),
                DescribeRole.Theorem))));
    }
}
