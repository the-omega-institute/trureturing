using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class ZigzagNaturalLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/carlsson2008zigzag");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A terminal endomorphism preserving the right filtration of a right-streamlined zigzag has exactly one natural lift.",
        H("Reconstructing endomorphisms of actual zigzags"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unique-natural-endomorphism"),
                DeclarationHandle.Create(Prefix + "exists_unique_natural_endomorphism"),
                H("Unique reconstruction from the terminal right filtration"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "K is any field. A prefix with vertices 0 through n contains one actual "
                        + "linear arrow of either orientation at each adjacent pair. Every forward "
                        + "arrow is injective and every backward arrow is surjective. The right "
                        + "filtration starts with zero and the first whole space. A forward step "
                        + "maps each old layer and appends the new whole space; a backward step "
                        + "prepends zero and takes inverse images of all old layers.")),
                    Paragraph(Text(
                        "For every linear endomorphism a of the terminal space preserving every "
                        + "right-filtration layer, there exists exactly one natural endomorphism "
                        + "of the actual finite oriented path-category diagram whose terminal "
                        + "component is a. No compatible family, lift or naturality is assumed. "
                        + "The diagram evaluates each path by composing its actual arrows.")),
                    Paragraph(Text(
                        "Backward induction restricts through an injective forward arrow and "
                        + "descends through the kernel quotient of a surjective backward arrow. "
                        + "Layer preservation proves that these predecessor maps preserve the "
                        + "predecessor filtration. The same injection or surjection forces each "
                        + "predecessor component. Path induction proves all naturality squares.")),
                    Paragraph(Text(
                        "The endomorphism remark after Lemma 3.18 in Carlsson and de Silva, "
                        + "PDF pages 16 and 17, is the source. Zero vertices and arbitrary "
                        + "characteristic are included; finite dimensionality is unnecessary for "
                        + "this reconstruction. The prefix has n+1 vertices, so n=0 means a "
                        + "single vertex. A chain with no vertices has no terminal component. "
                        + "General interval classification and intrinsic occurrence uniqueness "
                        + "are separate conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ResultFormula()
    {
        Formula field = F.Id("K"), zigzag = F.Id("D"), endomorphism = F.Id("a");
        Formula hypotheses = new Formula.Logic(Call("Field", field), FormulaLogicOperator.And,
            new Formula.Logic(Call("RightStreamlined", zigzag, F.Id("n")), FormulaLogicOperator.And,
                Call("PreservesEveryRightFiltrationLayer", zigzag, F.Id("n"), endomorphism)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("K", F.Id("Type")), Bound("D", Call("ActualZigzag", field)),
             Bound("n", Call("Nat")), Bound("a", Call("TerminalLinearEndomorphism", zigzag, F.Id("n")))],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
                Call("ExistsUniqueNaturalEndomorphismWithTerminalComponent", zigzag, F.Id("n"), endomorphism))));
    }
}
