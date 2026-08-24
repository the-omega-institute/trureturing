using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class LeastCommonReadoutRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical joint readout is the least common refinement and realizes kernel intersection.",
        H("Least Common Readout Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-readout-is-the-least-common-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/LeastCommonReadoutRefinement."
                        + "least_common_readout_refinement"),
                H("The joint readout is the least common refinement"),
                StatementSource.FromAuthor(UniversalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readouts q_J and q_K share an arbitrary source X. Their joint "
                            + "readout is the canonical conceptJoin, which records the pair of "
                            + "component values without introducing a second join primitive.")),
                    Paragraph(Text(
                        "The first two public conjuncts are the projection refinements. The "
                            + "third quantifies over every competing readout and states the "
                            + "universal factorization through any common refinement.")),
                    Paragraph(Text(
                        "The final public conjunct identifies the joint kernel with the "
                            + "intersection of the component kernels. This is the relation used "
                            + "by the repository's canonical quotient construction.")),
                    Paragraph(Text(
                        "Both results are direct applications of the frozen concept-family "
                            + "universal property and kernel-order duality theorem."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula UniversalFormula()
    {
        Formula source = F.Id("X");
        Formula firstType = F.Id("C");
        Formula secondType = F.Id("D");
        Formula comparisonType = F.Id("E");
        Formula first = Subscript(F.Id("q"), F.Id("J"));
        Formula second = Subscript(F.Id("q"), F.Id("K"));
        Formula comparison = Subscript(F.Id("q"), comparisonType);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula readout(Formula codomain) => Seq(source, Sp, To, Sp, codomain);
        Formula join = Join(first, second);
        Formula universal = Seq(
            Forall, Sp, comparisonType, Colon, Sp, type, Comma, Sp,
            comparison, Colon, Sp, readout(comparisonType), Comma, Sp,
            Refines(first, comparison), Sp, Rightarrow, Sp,
            Refines(second, comparison), Sp, Rightarrow, Sp,
            Refines(join, comparison));
        Formula kernelIntersection = Seq(
            Call("ker", join), Sp, Eq, Sp,
            Call("intersection", Call("ker", first), Call("ker", second)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, firstType, Comma, Sp, secondType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            first, Colon, Sp, readout(firstType), Comma, Sp,
            second, Colon, Sp, readout(secondType), Comma, RowBreak, Grp(),
            Refines(first, join), Sp, Land, RowBreak, Grp(),
            Refines(second, join), Sp, Land, RowBreak, Grp(),
            Open, universal, Close, Sp, Land, RowBreak, Grp(),
            kernelIntersection, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
