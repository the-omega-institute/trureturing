using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeDeletionEquivDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mamede2026commutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Excursion deletion equates the actual first-orientation singleton-word fibers.",
        H("First-Orientation Deletion Equivalence"),
        Blocks(
            Paragraph(Text("Fix exactSourceHypotheses(n,m,M,i,j,sigma). Let gamma be "
                + "wordProduct(n,deletedExcursion(m,M,i)) and pi=sigma*gamma inverse. "
                + "The quantification is over every n,m,M,i,j and sigma satisfying "
                + "the exact source condition, including i=j and empty outer words. "
                + "Fiber(n,tau) is the subtype of lists a with singletonWord(n,tau,a); "
                + "Equiv(A,B) is the type of equivalences between A and B, and val "
                + "forgets the subtype proof. ExactSource, SourceShape, Image and "
                + "Deleted denote exactSourceHypotheses, sourceShape, imageWord and "
                + "deletedExcursion respectively.")),
            Describe.Lean(
                DescribeId.Create("mamede-first-orientation-deletion-equivalence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Permutations/MamedeDeletionEquiv.source_deletion_equiv"),
                H("Deletion equates source and target singleton fibers"),
                StatementSource.FromAuthor(EquivalenceStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("There exists an equivalence between actual "
                    + "singletonWord fibers of sigma and pi. For every source word a "
                    + "and every sourceShape(m,M,i,j,a,p,q), its forward value is "
                    + "imageWord(i,j,p,q), and length(a) equals length(imageWord) "
                    + "plus the strictly positive length of deletedExcursion. "
                    + "Forward consecutive validity and reducedness are proved; "
                    + "injectivity recovers the first j marker without restricting "
                    + "the suffix. Surjectivity uses the existing conditional lift "
                    + "after extracting an actual shaped source. The paper's "
                    + "Proposition 3.8 supplies the injection context, but does "
                    + "not claim this equivalence. Reflected and oscillating cases "
                    + "and Conjecture 5.1 remain open."))),
                DescribeRole.Theorem))));

    private static Formula EquivalenceStatement()
    {
        var source = Call("Fiber", V("n"), V("sigma"));
        var target = Call("Fiber", V("n"), V("pi"));
        var a = Call("val", V("a"));
        var image = Call("val", Call("e", V("a")));
        var deleted = Call("Deleted", V("m"), V("M"), V("i"));
        var body = Q(
            Call("SourceShape", V("m"), V("M"), V("i"), V("j"), a, V("p"), V("q")),
            Implies, image, Eq, Call("Image", V("i"), V("j"), V("p"), V("q")),
            Land, Call("length", a), Eq, Call("length", image), Plus, Call("length", deleted),
            Land, D(0), Lt, Call("length", deleted));
        foreach (var name in new[] { "q", "p" })
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
                Call("List", V("Nat")), body);
        body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("a"), source, body);
        body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("e"),
            Call("Equiv", source, target), body);
        return Disp(Q(
            Call("ExactSource", V("n"), V("m"), V("M"), V("i"), V("j"), V("sigma")),
            Implies, body));
    }

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
