using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class AlgebraDescentEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent is equivalent to closure of the pullback algebra and effective-image observables.",
        H("Algebra Descent Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("descent-algebra-closure-tfae"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Dialectics/AlgebraDescentEquivalence."
                        + "descent_algebra_closure_tfae"),
                H("Descent and observable closure are equivalent"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state update descends to the canonical effective image of q "
                            + "exactly when the pullback algebra of q is closed under the "
                            + "update.")),
                    Paragraph(Text(
                        "The third clause makes the dual statement explicit: every observable "
                            + "on the effective image, when pulled back to states, has a "
                            + "next-step value that is again a function of the current "
                            + "effective readout.")),
                    Paragraph(Text(
                        "The effective-image carrier is the canonical subtype-valued "
                            + "realizedReadout, so the observable clause exposes the same "
                            + "interface object as the descent clause."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        DefinitionDsl.Call(name, arguments);

    private static Formula Statement()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula readout = F.Id("q");
        Formula update = F.Id("F");
        Formula canonical = Call("realizedReadout", readout);
        Formula conditions = Grp(
            OpenBracket,
            Call("EffectiveDescent", readout, update), Comma, Sp,
            Call("PullbackInvariant", readout, update), Comma, Sp,
            Call("ObservableInvariant", canonical, update),
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, RowBreak, Grp(),
            Call("ListTFAE", conditions), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
