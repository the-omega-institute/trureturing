using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class GettierWitnessDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Epistemic/GettierWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gettier witness is justified true belief accompanied by an admissible "
            + "same-evidence counterexample.",
        H("Gettier Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gettier-witness-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "gettier"),
                H("Gettier witness"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a state type and B an evidence type. Fix a state "
                            + "predicate P, evidence map E, evidence-indexed belief "
                            + "operator Bel, justification predicate Just, admissibility "
                            + "predicate Adm, and anchor a.")),
                    Paragraph(Text(
                        "The anchor satisfies P, Bel receives E and affirms P at a, and "
                            + "Just affirms P for E(a). In addition, an admissible witness "
                            + "x has exactly the same evidence as a while P(x) is false.")),
                    Paragraph(Text(
                        "The source ends immediately after the displayed definition. No "
                            + "conclusion after that truncation is supplied here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gettier-concrete-examples"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "gettier_concrete_examples"),
                H("Concrete positive and negative instances"),
                StatementSource.FromAuthor(ExampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take natural-number states with P true exactly at 0, constant "
                            + "evidence E(n) = 7, justification true exactly for evidence "
                            + "7, and admissibility true exactly at state 1.")),
                    Paragraph(Text(
                        "When belief is true exactly at anchor 0, state 1 is the required "
                            + "admissible counterexample: E(1) = E(0) = 7 and P(1) is "
                            + "false, while all three anchor clauses hold.")),
                    Paragraph(Text(
                        "Keeping every other component fixed but requiring belief at state "
                            + "1 breaks the belief clause at anchor 0, since 0 is not 1. "
                            + "Thus the first instance satisfies gettier and the second does "
                            + "not."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula DefinitionFormula()
    {
        Formula predicate = F.Id("P");
        Formula evidence = F.Id("E");
        Formula belief = F.Id("Bel");
        Formula justified = F.Id("Just");
        Formula admissible = F.Id("Adm");
        Formula anchor = F.Id("a");
        Formula witness = F.Id("x");
        Formula gettier = Apply(
            "gettier", predicate, evidence, belief, justified, admissible, anchor);

        return Disp(Seq(
            gettier, Sp, Iff, RowBreak, Grp(),
            Apply("P", anchor), Sp, Land, RowBreak, Grp(),
            Apply("Bel", evidence, predicate, anchor), Sp, Land, RowBreak, Grp(),
            Apply("Just", Apply("E", anchor), predicate), Sp, Land, RowBreak, Grp(),
            Exists, Sp, witness, Comma, Sp,
            Apply("Adm", witness), Sp, Land, Sp,
            Apply("E", witness), Sp, Eq, Sp, Apply("E", anchor), Sp, Land, Sp,
            Neg, Apply("P", witness), Dot));
    }

    private static Formula ExampleFormula()
    {
        Formula predicate = F.Id("P");
        Formula evidence = F.Id("E");
        Formula beliefAtZero = F.Id("Bel_0");
        Formula beliefAtOne = F.Id("Bel_1");
        Formula justified = F.Id("Just");
        Formula admissible = F.Id("Adm");
        Formula state = F.Id("n");
        Formula value = F.Id("e");
        Formula zero = D(0);
        Formula one = D(1);
        Formula seven = D(7);
        Formula positive = Apply(
            "gettier", predicate, evidence, beliefAtZero, justified, admissible, zero);
        Formula negative = Apply(
            "gettier", predicate, evidence, beliefAtOne, justified, admissible, zero);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Apply("P", state), Sp, Iff, Sp, state, Sp, Eq, Sp, zero, Comma, Sp,
            Apply("E", state), Sp, Eq, Sp, seven, Comma, RowBreak, Grp(),
            Apply("Bel_0", evidence, predicate, state), Sp, Iff, Sp,
            state, Sp, Eq, Sp, zero, Comma, Sp,
            Apply("Bel_1", evidence, predicate, state), Sp, Iff, Sp,
            state, Sp, Eq, Sp, one, Comma, RowBreak, Grp(),
            Apply("Just", value, predicate), Sp, Iff, Sp,
            value, Sp, Eq, Sp, seven, Comma, Sp,
            Apply("Adm", state), Sp, Iff, Sp, state, Sp, Eq, Sp, one, Comma,
            RowBreak, Grp(),
            positive, Sp, Land, Sp, Neg, negative, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
