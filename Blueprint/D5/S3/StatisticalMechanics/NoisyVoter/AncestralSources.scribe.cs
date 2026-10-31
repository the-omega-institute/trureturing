using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class AncestralSourcesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ancestral sources give a degree-independent native repetition variance bound.",
        H("Ancestral collisions and repetition variance"),
        Blocks(
            Paragraph(Text("Initial opinions and positive-time fresh opinions have disjoint labels. A fresh label records its positive natural birth time and vertex. At time zero the source is the initial coordinate. A refresh selects the corresponding fresh coordinate. A copy follows the actual chosen neighbour into the preceding time layer.")),
            Node("native-source", "native_source", "Reconstruction of the actual opinion", NativeSource(),
                "For every coordinate assignment, vertex, natural time and sample point, the native opinion equals the coin at its source label. The identity is pathwise and includes time zero."),
            Node("uniform-variance-lower", "uniform_variance_lower", "The degree-independent finite-time lower bound", UniformLower(),
                "For every instance of the existing native Model, Var(W_t) is at least t(1-(1-epsilon)^d)/4 for every vertex and natural d,t. This includes finite and infinite connected locally finite graphs and uses that model's original probability space and joint coordinate law. The empty time sum and lag zero give a zero lower bound. At lag two the expression is the lower endpoint required by the source Theorem 3.2."),
            Paragraph(Text("The proof uses deterministic finite source support to establish measurability. The complete source field is independent of the labelled fair opinion coins. Consequently, a two-opinion sign moment is its source-collision probability, and a four-opinion sign moment is the probability of an even pairing of its four sources. The pairing events form a union and can overlap; their probabilities are not added.")),
            Paragraph(Text("Comparing the sign-product covariance with the covariance of the source-collision indicators leaves nonnegative off-diagonal contributions and an unequal-source probability on the diagonal. The variance of the collision-indicator sum is nonnegative. A collision across lag d requires survival without refresh through those d layers, whose probability is (1-epsilon)^d under the actual joint law.")),
            Paragraph(Text("The native Model also prescribes independent fresh, refresh and choice coordinates at time zero. A bridge from every realization prescribing those families only at positive times has not been established here. The result also does not give the K2 finite-time independence and variance identity, construct the full optimal-constant infimum, or prove its upper endpoint, endpoint ratio, polynomial bracket and asymptotic clauses. It makes no assertion about exact-infimum attainment or existence of a normalized limit."))), []));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("voter-source-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula DepArr(string name, Formula type, Formula body) =>
        Seq(Open, F.Id(name), Colon, type, Close, Sp, To, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Proj(string name) => Seq(F.Id("M"), Dot, Named(name));
    private static Formula Binary(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Base(Formula body) => All("V", Named("Type"), All("O", Named("Type"),
        All("G", App(Named("SimpleGraph"), F.Id("V")), body)));

    private static Formula NativeSource() => Disp(Base(All("x",
        DepArr("c", App(Named("Coord"), F.Id("V")),
            Arr(F.Id("O"), App(Named("Value"), F.Id("G"), F.Id("c")))),
        All("n", Nat(), All("v", F.Id("V"), All("w", F.Id("O"),
            Eqn(App(Named("nvm"), F.Id("x"), F.Id("n"), F.Id("v"), F.Id("w")),
                App(Named("coin"), F.Id("x"),
                    App(Named("source"), F.Id("x"), F.Id("n"), F.Id("v"), F.Id("w")),
                    F.Id("w")))))))));

    private static Formula UniformLower()
    {
        var one = new Formula.Number(1);
        var epsilon = Seq(Open, F.Id("M"), Dot, Varepsilon, Colon, Real(), Close);
        var q = Binary(one, FormulaBinaryOperator.Subtract, epsilon);
        var qPower = Seq(Open, q, Close, Caret, Grp(F.Id("d")));
        var lower = Binary(Seq(Frac, Grp(Seq(Open, F.Id("t"), Colon, Real(), Close)),
                Grp(new Formula.Number(4))), FormulaBinaryOperator.Multiply,
            Binary(one, FormulaBinaryOperator.Subtract, qPower));
        var variance = App(Named("variance"),
            App(Named("W"), Proj("coordinate"), F.Id("u"), F.Id("d"), F.Id("t")), F.Id("P"));
        return Disp(Base(Inst(Seq(F.Id("G"), Dot, Named("LocallyFinite")),
            Inst(App(Named("MeasurableSpace"), F.Id("O")),
                All("P", App(Named("Measure"), F.Id("O")),
                    All("M", App(Named("Model"), F.Id("G"), F.Id("P")),
                        All("u", F.Id("V"), All("d", Nat(), All("t", Nat(),
                            new Formula.Relation(lower, FormulaRelationOperator.LessThanOrEqual, variance))))))))));
    }
}
