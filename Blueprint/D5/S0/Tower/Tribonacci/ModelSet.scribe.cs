using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciModelSetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var z = Id("z");
        var name = Id("name");
        var complexes = Id("C");
        var naturals = Id("N");
        var names = Call("TribonacciName", q);
        var coordinate = Call("conjugateCoordinate", z, name);
        var window = Call("tribonacciInternalWindow", z);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Tribonacci names have bounded internal coordinates at every secondary root.",
            H("Tribonacci Bounded Internal Window"),
            Blocks(
                Paragraph(Text(
                    "The scope is the bounded-window core of a cut-and-project argument. "
                    + "The formalization does not construct an ambient lattice or a complete "
                    + "cut-and-project scheme, and it does not claim that the physical set is "
                    + "Delone, Meyer, uniformly discrete, or relatively dense.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-conjugate-coordinate"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ModelSet.conjugateCoordinate"),
                    H("Conjugate coordinate"),
                    StatementSource.FromAuthor(Equal(
                        coordinate,
                        Call("digitPolynomialEvaluation", name, z))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A finite admissible name is evaluated as a zero-one digit polynomial "
                        + "at the chosen complex root."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-conjugate-embedding-is-injective"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ModelSet.conjugate_embedding_injective"),
                    H("Fixed-layer decoded-internal coordinates are injective"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("z"),
                            complexes,
                            Call(
                                "Injective",
                                Call("conjugateEmbeddingAtLength", q, z))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The first component is the frozen integer decoder. Its fixed-layer "
                        + "injectivity therefore makes the paired decoded-internal map injective."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("contracting-conjugate-coordinate-has-geometric-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ModelSet.conjugate_coordinate_norm_le"),
                    H("Contracting coordinates have a geometric-series bound"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("name"),
                            names,
                            new Formula.Bind(
                                FormulaQuantifier.ForAll,
                                FormulaIdentifier.Create("z"),
                                complexes,
                                Call(
                                    "Implies",
                                    Call("LessThan", Call("abs", z), Num(1)),
                                    Call(
                                        "LessEqual",
                                        Call("abs", coordinate),
                                        Call("inverseOneMinusAbs", z))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The triangle inequality bounds every zero-one digit sum by a finite "
                        + "geometric sum, which is bounded by the full convergent series."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-secondary-root-window-is-bounded"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ModelSet."
                        + "tribonacci_internal_window_is_bounded"),
                    H("The Tribonacci internal window is bounded"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("z"),
                        complexes,
                        Call(
                            "Implies",
                            Call("SecondaryTribonacciRoot", z),
                            Call("Bounded", window)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen Pisot-root theorem supplies absolute value below one for "
                        + "every non-Perron root. The geometric estimate is uniform in the "
                        + "name length, so all finite internal coordinates lie in one bounded "
                        + "window."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Binet")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Representation")),
            ]));
    }
}
