using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FiniteSimplexSelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly positive normalized profiles with a singleton weight form a path-connected set when there are at least three labels.",
        H("Path connected weight profiles with an admissible choice"),
        Blocks(Describe.Lean(
            DescribeId.Create("path-connected-normalized-singleton-profiles"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/FiniteSimplexSelection.pathConnected_normalized_profiles"),
            H("Positive normalized profiles with a singleton weight are path connected"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite label type I of cardinality at least three, consider all real profiles "
                        + "with strictly positive weights, sum one, and a weight occurring at exactly one "
                        + "label. The set of such profiles is path connected.")),
                Paragraph(Text(
                    "If every weight occurs more than once, each label admits a distinct peer of the same weight. "
                        + "A fixed-point-free map sending labels to such peers specifies a linear subspace "
                        + "by requiring all its peer equalities. The profiles without a singleton weight are "
                        + "the union of these finitely many subspaces. Each remains proper after adjoining "
                        + "any line. To see this, take a label i and a label k outside the pair formed by i and "
                        + "its peer. If the added vector agrees on the first pair, the coordinate spike at i "
                        + "is excluded. If it disagrees, any decomposition of the spike at k would force the "
                        + "coefficient of the added vector to vanish, which contradicts the peer equality at k.")),
                Paragraph(Text(
                    "The positive cone outside these subspaces is path connected. Dividing each vector by "
                        + "the sum of its weights is continuous there and preserves equality of coordinates. "
                        + "Its image is the stated subset of the probability simplex.")),
                Paragraph(Text(
                    "A continuous rule on this domain with discrete outcome labels would be constant by "
                        + "connectedness. A permutation moving the chosen label conflicts with equivariance. "
                        + "The assertion about continuous selection is a consequence of path connectedness "
                        + "and the permutation invariance of the domain."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula labels = F.Id("I");
        Formula weight = F.Id("w");
        Formula first = F.Id("i");
        Formula second = F.Id("j");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula singleton = Seq(Exists, Sp, first, Colon, labels, Comma, Sp,
            Forall, Sp, second, Colon, labels, Comma, Sp,
            Call("w", second), Sp, Eq, Sp, Call("w", first), Sp, Rightarrow, Sp, second, Sp, Eq, Sp, first);
        Formula positive = Seq(Forall, Sp, first, Colon, labels, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("w", first));
        Formula profiles = Seq(OpenBrace, weight, Colon, new Formula.TypeArrow(labels, real), Sp, Mid, Sp,
            Open, positive, Close, Sp, Land, Sp, Call("sum", weight), Sp, Eq, Sp, D(1),
            Sp, Land, Sp, Open, singleton, Close, CloseBrace);
        return Disp(Seq(Forall, Sp, labels, Colon, type, Comma, Sp,
            OpenBracket, Call("Fintype", labels), CloseBracket, Comma, Sp,
            D(2), Sp, Lt, Sp, Call("card", labels), Sp, Rightarrow, Sp,
            Call("IsPathConnected", profiles)));
    }
}
