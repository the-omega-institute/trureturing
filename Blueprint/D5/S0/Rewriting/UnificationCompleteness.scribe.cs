using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class UnificationCompletenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/UnificationCompleteness.";
    private static DocumentBlock Entry(string id, string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted finite unification completeness.", H("Unrestricted finite unification completeness"), Blocks(
            Paragraph(Text("The soundness, MGU, absorption, occurs and zipped-constructor suppliers are consumed faithful Strata reuse in this same owning unit. Unrestricted completeness is proved by mutual induction over the unchanged algorithm, using one arbitrary common substitution and the actual returned head state. The solution substitution has no well-formedness, groundness or separated-variable premise.")),
            Entry("unifyone-complete", "unifyOne_complete", "A common solution prevents single-equation failure", "For every equation c, well-formed current state S, and arbitrary finite substitution R, if R solves c and absorbs S, the actual Constraint.unifyOne call returns a successful relation. There is no well-formedness, groundness or disjoint-variable condition on R.", DescribeRole.Theorem),
            Entry("unifycore-complete", "unifyCore_complete", "Completeness through the returned states", "For every finite equation list, current state and common substitution solving every equation and absorbing the current state, Constraints.unifyCore succeeds. The tail receives the substitution returned from the head, and the original MGU absorption law carries the same common substitution to that state.", DescribeRole.Theorem),
            Entry("unify-complete", "unify_complete", "Unrestricted failure completeness", "For arbitrary equations C, current SubstInfo S and Subst R, solving all of C and absorbing S implies existence of an output T with Constraints.unify C S = ok T. The occurs-check obstruction is valid for arbitrary R; constructor equality supplies every zipped argument equation.", DescribeRole.Theorem))));
}
