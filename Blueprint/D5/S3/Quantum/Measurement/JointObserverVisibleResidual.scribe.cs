using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class JointObserverVisibleResidualDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/JointObserverVisibleResidual."
            + "joint_observer_visible_and_residual";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint effect families add visible directions and intersect invisible residuals.",
        H("Joint Observer Visible Space and Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-observer-visible-space-and-residual"),
                DeclarationHandle.Create(Declaration),
                H("Joint observers add visibility and intersect residuals"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite matrix dimension d, each observer is represented by an "
                            + "arbitrary set of effects in the canonical real Hermitian space. "
                            + "Its visible space is the real span of the identity together with "
                            + "those effects.")),
                    Paragraph(Text(
                        "The joint observer is constructed from the union of the two effect "
                            + "sets. Its visible space is the submodule join of the individual "
                            + "visible spaces, and its Hilbert--Schmidt orthogonal residual is "
                            + "the submodule meet of the individual residuals.")),
                    Paragraph(Text(
                        "The proof applies the pinned library identities for the span of a set "
                            + "union and for the orthogonal complement of a submodule join."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula effectsOne = F.Id("E1");
        Formula effectsTwo = F.Id("E2");
        Formula carrier = Call("HermitianSpace", d);
        Formula identity = Call("identityHermitian", d);
        Formula effectSet = Call("Set", carrier);
        Formula Visible(Formula effects) =>
            Call("span", real, Call("insert", identity, effects));
        Formula jointEffects = Call("union", effectsOne, effectsTwo);
        Formula jointVisible = Visible(jointEffects);
        Formula firstVisible = Visible(effectsOne);
        Formula secondVisible = Visible(effectsTwo);
        Formula Orthogonal(Formula subspace) => Call("orthogonal", subspace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, d, Colon, Sp, F.Id("Nat"), Comma, Sp,
                effectsOne, Comma, Sp, effectsTwo, Colon, Sp, effectSet, Comma),
            Seq(
                jointVisible, Sp, Eq, Sp,
                Call("join", firstVisible, secondVisible), Sp, Land, Sp),
            Seq(
                Orthogonal(jointVisible), Sp, Eq, Sp,
                Call("meet", Orthogonal(firstVisible), Orthogonal(secondVisible)), Dot),
        ]));
    }
}
