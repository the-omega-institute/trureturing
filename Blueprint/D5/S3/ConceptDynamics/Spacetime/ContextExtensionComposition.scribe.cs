using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ContextExtensionCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sequential context embeddings compose, and their new-region charges add.",
        H("Context Extension Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("context-extension-composition-full-spec"),
                DeclarationHandle.Create(Prefix + "context_extension_composition_spec"),
                H("Composition transports q and splits the new region"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Given embeddings j from C to D and k from D to E, their archive and "
                            + "current-region maps compose. The new region of the composite is "
                            + "the disjoint union of the second new region and the image of the "
                            + "first new region.")),
                    Paragraph(Text(
                        "The signed charge therefore adds across the two extension steps, while "
                            + "the selected q readout is transported unchanged through both maps."))),
                DescribeRole.Proposition)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement"))
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula R(string suffix) =>
        new Formula.Subscript(F.Id("R"), F.Id(suffix));

    private static Formula TheoremFormula()
    {
        Formula c = F.Id("C"), d = F.Id("D"), e = F.Id("E"), a = F.Id("A");
        Formula j = F.Id("j"), k = F.Id("k");
        Formula qTransport = Equal(Call("q", e, Call("k", Call("j", a))),
            Call("q", c, a));
        Formula split = Equal(R("jk"),
            Seq(R("k"), Sp, Cup, Sp, Call("k", R("j"))));
        Formula disjoint = Call("Disjoint", R("k"), Call("k", R("j")));
        Formula charge = Equal(Call("charge", e, R("jk")),
            new Formula.Binary(Call("charge", e, R("k")),
                FormulaBinaryOperator.Add, Call("charge", e, Call("k", R("j")))));
        return Disp(Seq(qTransport, Comma, Sp,
            And(split, And(disjoint, charge)), Dot));
    }
}
