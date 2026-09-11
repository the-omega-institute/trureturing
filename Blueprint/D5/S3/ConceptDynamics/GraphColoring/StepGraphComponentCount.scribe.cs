using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class StepGraphComponentCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive fixed step partitions an integer interval into its occurring residue classes.",
        H("Fixed-step graph components"),
        Blocks(
            Entry("graph", "stepGraph", "The interval graph",
                "The vertices are 0 through d-1. The undirected graph joins i and j when "
                    + "i+m=j or j+m=i, and removes loops. For m at least one, this is exactly "
                    + "the condition that the absolute difference of the labels equals m.",
                Disp(Seq(Call("G", D, M), Sp, Eq, Sp,
                    Call("fromRel", Seq(LambdaLower, Sp, F.Id("i"), Sp, F.Id("j"), Comma, Sp,
                        F.Id("i"), Plus, M, Eq, F.Id("j"))))), DescribeRole.Definition),
            Entry("residues", "occurringResidues", "The occurring residues",
                "Take the image of the interval under reduction modulo m. Repeated residues "
                    + "are counted once, and residues not represented by any vertex are absent.",
                Disp(Seq(Call("R", D, M), Sp, Eq, Sp,
                    OpenBrace, Call("mod", F.Id("i"), M), Sp, Mid, Sp,
                    Num(0), Sp, Le, Sp, F.Id("i"), Sp, Lt, Sp, D, CloseBrace)), DescribeRole.Definition),
            Entry("reachability", "reachable_iff_mod_eq", "Reachability is equality of residues",
                "Let d and m be natural numbers with m at least one, and let i and j be "
                    + "vertices. Every edge preserves the remainder, so every finite walk "
                    + "preserves it. Conversely, repeatedly subtracting m from a label at "
                    + "least m stays in the interval and eventually reaches its remainder. "
                    + "Reversing one such walk connects any two labels with the same remainder.",
                Disp(Seq(Call("Reachable", Call("G", D, M), F.Id("i"), F.Id("j")),
                    Sp, Iff, Sp, Call("mod", F.Id("i"), M), Sp, Eq, Sp,
                    Call("mod", F.Id("j"), M)))),
            Entry("bijection", "componentEquivResidues", "Components and occurring residues",
                "For every d and positive m, assign each component the remainder of any "
                    + "of its vertices. Preservation along walks makes this independent of "
                    + "the chosen vertex. Equal remainders give a walk, proving injectivity; "
                    + "each occurring remainder has a vertex, proving surjectivity.",
                Disp(Seq(Call("ConnectedComponent", Call("G", D, M)), Sp,
                    Equiv, Sp, Call("R", D, M))), DescribeRole.Definition),
            Entry("count", "connectedComponent_card", "The number of components",
                "For arbitrary natural d and m with m at least one, the occurring residues "
                    + "are exactly 0 through min(m,d)-1. Every remainder is below m and no "
                    + "larger than its original label; each label below both bounds represents "
                    + "itself. The component bijection therefore gives the stated cardinality. "
                    + "When d is zero both sets are empty. When m is at least d every vertex "
                    + "is isolated; when d is one there is one component. Positivity of m is "
                    + "necessary: at m=0 and d=1 the loopless graph has one component, "
                    + "whereas min(0,1)=0.",
                Disp(Seq(Forall, Sp, D, Comma, M, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))),
                    Comma, Sp, Num(1), Sp, Le, Sp, M, Sp, Rightarrow, Sp,
                    Call("card", Call("ConnectedComponent", Call("G", D, M))),
                    Sp, Eq, Sp, Call("min", M, D)))))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose,
        Formula formula, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("stepgraph-" + id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula D => F.Id("d");
    private static Formula M => F.Id("m");
}
