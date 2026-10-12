using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class NativeTermUnificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/NativeTermUnification.";
    private static DocumentBlock Entry(string id, string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native fragment preservation by the original algorithm.", H("Native fragment preservation by the original algorithm"), Blocks(
            Paragraph(Text("Constraint.unifyOne, Constraints.unifyCore and Constraints.unify retain the pinned Strata algorithm, including actual returned states and termination proofs. The new native invariant follows the same mutual recursion; neither the algorithm nor its accepted syntax is redesigned.")),
            Entry("unifyone-native", "unifyOne_native", "Every successful equation step", "For every equation, current state, returned relation and actual success equality, native input terms and native current substitution values imply native returned substitution values. Both variable orientations, existing bindings, fresh bindings and decomposed constructor equations are included.", DescribeRole.Theorem),
            Entry("unifycore-native", "unifyCore_native", "Every successful list step", "For every equation list, state and successful returned relation, native current values and native terms on both sides of every equation imply native output values.", DescribeRole.Theorem),
            Entry("unify-native", "unify_native", "Successful native output", "For every successful actual unify call, native equations and native current substitution values imply native output values. Free-variable bounds alone do not establish this constructor invariant.", DescribeRole.Theorem))));
}
