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
                        "Let j map the archive of C injectively into that of D, and k map the "
                            + "archive of D injectively into that of E. Each map preserves time, "
                            + "position, sign, and source tree, and preserves and reflects causality. "
                            + "Their full current-region guards are j(x) in OmegaD iff x in OmegaC, "
                            + "and k(y) in OmegaE iff y in OmegaD, for every archived x and y. "
                            + "Equivalently j[OmegaC] = intersection(OmegaD, range(j)), and "
                            + "k[OmegaD] = intersection(OmegaE, range(k)). The composite ell "
                            + "is defined pointwise by ell(x) = k(j(x)); it preserves this full "
                            + "guard, including no reactivation of old noncurrent events. "
                            + "Square brackets denote direct images. Put Rj = OmegaD minus "
                            + "j[OmegaC], Rk = OmegaE minus k[OmegaD], and Rell = OmegaE "
                            + "minus ell[OmegaC]. Let A be any selection contained in OmegaC.")),
                    Paragraph(Text(
                        "The signed charge therefore adds across the two extension steps, while "
                            + "the selected q readout is transported unchanged through both maps. "
                            + "This composition API is a companion result; no separate source "
                            + "coverage is asserted for it."))),
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

    private static Formula Image(string name, Formula region) =>
        Seq(F.Id(name), OpenBracket, region, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula c = F.Id("C"), d = F.Id("D"), e = F.Id("E"), a = F.Id("A");
        Formula transported = Image("k", Image("j", a));
        Formula selection = Equal(Image("ell", a), transported);
        Formula split = Equal(R("ell"),
            Seq(R("k"), Sp, Cup, Sp, Image("k", R("j"))));
        Formula disjoint = Call("Disjoint", R("k"), Image("k", R("j")));
        Formula charge = Equal(Call("charge", e, R("ell")),
            new Formula.Binary(Call("charge", e, R("k")),
                FormulaBinaryOperator.Add, Call("charge", d, R("j"))));
        Formula qTransport = Equal(Call("q", e, transported), Call("q", c, a));
        return Disp(And(selection, And(split, And(disjoint, And(charge, qTransport)))));
    }
}
