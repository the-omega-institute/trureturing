using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class CoordinateDeletionRobustnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One more separating coordinate than the deletion budget preserves joint faithfulness.",
        H("Coordinate-Deletion Robustness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-deletion-robustness"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Faithfulness/CoordinateDeletionRobustness."
                        + "coordinate_deletion_robustness"),
                H("Redundant separation survives bounded coordinate deletion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every distinct pair of states, the premise supplies a finite set "
                            + "of exactly f + 1 coordinates whose readouts separate that pair. "
                            + "This witness form states the source's at-least condition without "
                            + "requiring decidable equality on any output carrier.")),
                    Paragraph(Text(
                        "A deleted coordinate set of cardinality at most f cannot contain the "
                            + "entire separating witness. Evaluating equal surviving joint "
                            + "readouts at a witness outside the deleted set contradicts its "
                            + "separation property.")),
                    Paragraph(Text(
                        "The conclusion uses the existing dependent jointReadout on the subtype "
                            + "of coordinates outside the deleted set, so completeness is "
                            + "injectivity of the canonical surviving observation family."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Read(Formula readout, Formula index, Formula state) =>
        Call("q", index, state);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula outputFamily = F.Id("O");
        Formula readout = F.Id("q");
        Formula budget = F.Id("f");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula index = F.Id("i");
        Formula separating = F.Id("S");
        Formula deleted = F.Id("D");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula readoutType = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            stateType, Sp, To, Sp, Apply(outputFamily, index));
        Formula separates = Seq(
            Exists, Sp, separating, Colon, Sp, Call("Finset", indexType), Comma, Sp,
            Call("card", separating), Sp, Eq, Sp, budget, Sp, Plus, Sp, D(1), Sp, Land, Sp,
            Forall, Sp, index, Colon, Sp, separating, Comma, Sp,
            Read(readout, index, left), Sp, Neq, Sp, Read(readout, index, right));
        Formula redundancy = Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, stateType, Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Rightarrow, Sp, Open, separates, Close);
        Formula survivors = Seq(
            OpenBrace, index, Colon, Sp, indexType, Sp, Mid, Sp,
            Neg, Open, index, Sp, InMacro, Sp, deleted, Close, CloseBrace);
        Formula survivingReadout = Call("restrict", readout, survivors);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp, type, Comma, Sp,
                outputFamily, Colon, Sp, Arrow(indexType, type), Comma),
            Seq(
                readout, Colon, Sp, readoutType, Comma, Sp,
                budget, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma),
            Seq(Open, redundancy, Close, Sp, Rightarrow),
            Seq(
                Forall, Sp, deleted, Colon, Sp, Call("Finset", indexType), Comma, Sp,
                Call("card", deleted), Sp, Leq, Sp, budget, Sp, Rightarrow),
            Seq(
                Call("Injective", Call("jointReadout", survivingReadout)), Dot),
        ]));
    }
}
