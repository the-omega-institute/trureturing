using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class DenseNamingBoundaryDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix = "D5/S0/Naming/DenseNamingBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separating discrete names force dense stated boundaries when every open region contains "
            + "a nontrivial connected piece.",
        H("Dense Naming Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dense-union-of-naming-boundaries"),
                DeclarationHandle.Create(DeclarationPrefix + "dense_iUnion_namingBoundary"),
                H("Separating discrete names have dense boundary union"),
                StatementSource.FromAuthor(DenseBoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume every nonempty open region contains an open preconnected subset "
                            + "with two distinct points. Each discrete-valued name is continuous "
                            + "off its stated boundary, and the complete family separates points.")),
                    Paragraph(Text(
                        "If some nonempty open region avoided every boundary, choose two distinct "
                            + "points in its preconnected piece. IsPreconnected.constant makes "
                            + "every name equal on that pair, contradicting separation.")),
                    Paragraph(Text(
                        "The local connected-piece premise corrects the unrestricted source claim. "
                            + "It is indispensable, as the following discrete counterexample shows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unrestricted-dense-boundary-counterexample"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "unrestricted_dense_boundary_fails"),
                H("The unrestricted dense-boundary claim fails on a discrete space"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On discrete Bool, repeat the identity name at every natural index and state "
                        + "every boundary to be empty. The names are continuous and separate the "
                        + "two points, but their boundary union is empty and hence not dense."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula DenseBoundaryFormula()
    {
        Formula x = F.Id("X");
        Formula names = Nu;
        Formula boundary = F.Id("B");
        Formula hypotheses = Seq(
            Call("HasNontrivialPreconnectedOpenPieces", x), Sp, Land, Sp,
            Call("ContinuousAway", names, boundary), Sp, Land, Sp,
            Call("SeparatesPoints", names));
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, names, Comma, Sp, boundary, Comma, RowBreak,
            hypotheses, Sp, Rightarrow, Sp,
            Call("Dense", Call("iUnion", boundary)), Dot));
    }

    private static Formula CounterexampleFormula()
    {
        Formula names = Nu;
        Formula boundary = F.Id("B");
        return Disp(Seq(
            Exists, Sp, names, Comma, Sp, boundary, Comma, RowBreak,
            Call("ContinuousAway", names, boundary), Sp, Land, Sp,
            Call("SeparatesPoints", names), Sp, Land, Sp,
            Neg, Call("Dense", Call("iUnion", boundary)), Dot));
    }
}
