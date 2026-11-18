using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class SalinasSchmeisLexicographicFiberExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisLexicographicFiberExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/salinasschmeis2026omega");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lexicographic extensions partitioned into inherited fibers.",
        H("Extensions by lexicographic fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lex-fiber"), DeclarationHandle.Create(Prefix + "lexFiber"),
                H("The first-coordinate fiber"), StatementSource.FromAuthor(Disp(FiberFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The carrier is Lex(Prod(P,A)), with the lexicographic partial order supplied "
                    + "by Mathlib. A fiber is the literal subset on which the first coordinate "
                    + "equals the index, with the order inherited from the product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lex-base-embedding"),
                DeclarationHandle.Create(Prefix + "lexBaseEmbedding"),
                H("The induced base embedding"), StatementSource.FromAuthor(Disp(BaseFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix a point of A. The map preserves and reflects the base order since the "
                    + "two second coordinates are the same. Equality of the lifted first "
                    + "coordinates also gives injectivity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lex-fiber-order-iso"),
                DeclarationHandle.Create(Prefix + "lexFiberOrderIso"),
                H("The inherited fiber order"), StatementSource.FromAuthor(Disp(FiberIsoFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Insert the second coordinate at the fixed first coordinate. The inverse "
                    + "reads the second coordinate, and the strict first-coordinate comparison "
                    + "is impossible within the fiber. The resulting comparison is exactly "
                    + "the comparison in A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lex-fiber-extension"),
                DeclarationHandle.Create(Prefix + "lexFiberExtension"),
                H("The literal fiber partition"), StatementSource.FromAuthor(Disp(ExtensionFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The base map is a section of first projection. Each literal fiber is the "
                        + "equivalence class of the corresponding base image for the kernel setoid "
                        + "of that projection. These classes partition the whole carrier. If P is "
                        + "empty, the carrier and the family of parts are both empty.")),
                    Paragraph(Text(
                        "Taking A to be the natural numbers and the distinguished point to be zero "
                        + "gives an induced extension of every partial order and an omega partition "
                        + "in the original IsExtension and OmegaPartitionable predicates.")),
                    Paragraph(Text(
                        "For any nonzero ordinal α in universe v, take A = α.ToType and choose "
                        + "the point represented by zero. The base may be in any independent universe u. "
                        + "Each part lies in universe max(u,v) and its inherited strict order has type "
                        + "Ordinal.lift to that universe applied to α. Lifting the ambient carrier "
                        + "upward again replaces each part by its preimage under ULift.down and "
                        + "lifts the order type accordingly. This covers α = 1, successors, limits "
                        + "and uncountable ordinals. The family is a skeleton in the sense of "
                        + "Definition 2.33 because it is disjoint and each point itself witnesses "
                        + "cofinality in its own part.")),
                    Paragraph(Text(
                        "The construction formalizes the existence proposition and the extension "
                        + "clause of the skeleton corollary in the revision-2 note by Haobo Ma "
                        + "(ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of "
                        + "Singapore and ChronoAI Pte Ltd, Singapore). The countable partition "
                        + "theorem and the general partition and lifting results remain credited "
                        + "to Remi Salinas Schmeis."))),
                DescribeRole.Theorem))));

    private static Formula FiberFormula()
    {
        var p = F.Id("p");
        var x = F.Id("x");
        return Carriers(All("p", F.Id("P"),
            Equal(Call("lexFiber", p), Seq(
                OpenBrace, x, Sp, InMacro, Sp, Product(), Sp, Mid, Sp,
                Equal(Seq(Call("ofLex", x), Dot, D(1)), p), CloseBrace))));
    }

    private static Formula BaseFormula()
    {
        var a = F.Id("a");
        var p = F.Id("p");
        return OrderedCarriers(All("a", F.Id("A"), All("p", F.Id("P"),
            Equal(App(Call("lexBaseEmbedding", a), p), Call("toLex", Pair(p, a))))));
    }

    private static Formula FiberIsoFormula()
    {
        var p = F.Id("p");
        var a = F.Id("a");
        return OrderedCarriers(All("p", F.Id("P"), All("a", F.Id("A"),
            Equal(Seq(Parenthesized(App(Call("lexFiberOrderIso", p), a)), Dot, F.Id("val")),
                Call("toLex", Pair(p, a))))));
    }

    private static Formula ExtensionFormula()
    {
        var p = F.Id("P");
        var point = F.Id("p");
        var literalFamily = App(Seq(Operatorname, Grp(F.Id("Set")), Dot, F.Id("range")),
            Seq(point, Sp, Mapsto, Sp, Call("lexFiber", point)));
        var partition = App(Seq(Operatorname, Grp(F.Id("Setoid")), Dot, F.Id("IsPartition")),
            literalFamily);
        var inherited = All("p", p,
            Call("Nonempty", Call("OrderIso", F.Id("A"), Call("lexFiber", point))));
        return OrderedCarriers(Seq(
            Forall, Sp, F.Id("a"), Sp, Colon, Sp, F.Id("A"), Comma, Sp,
            Call("IsExtension", p, Product()), Sp, Land, Sp,
            partition, Sp, Land, Sp, Parenthesized(inherited)));
    }

    private static Formula Carriers(Formula body) =>
        All("P", TypeAt("u"), All("A", TypeAt("v"), body));

    private static Formula OrderedCarriers(Formula body) =>
        Carriers(Seq(OpenBracket, Call("PartialOrder", F.Id("P")), CloseBracket, Sp,
            OpenBracket, Call("PartialOrder", F.Id("A")), CloseBracket, Sp, body));

    private static Formula TypeAt(string level) => Seq(F.Id("Type"), Sp, F.Id(level));

    private static Formula Product() => Call("Lex", Call("Prod", F.Id("P"), F.Id("A")));

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);

    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
