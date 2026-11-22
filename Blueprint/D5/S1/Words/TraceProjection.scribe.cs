using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TraceProjectionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/coriperrin1985traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered dependent-pair projections characterize finite words modulo partial commutation.",
        H("Dependent-Pair Projections of Finite Traces"),
        Blocks(
            Paragraph(Text("Let alpha be an arbitrary type in any universe, and let I be a "
                + "symmetric irreflexive relation on alpha. Words are native finite lists over "
                + "alpha. A legal step exchanges p ++ a :: b :: q with p ++ b :: a :: q when "
                + "I(a,b), leaving both contexts unchanged. Connected(I,s,t) is the reflexive "
                + "transitive closure of these steps. The independently defined readout "
                + "pairProjection(a,b,s) deletes every letter other than a or b and keeps "
                + "the original order. E(I,s,t), also called SameProjections, means equality "
                + "of these lists for every a,b with not I(a,b), including a=b. "
                + "EveryIndependent(I,a,p) means that I(a,b) holds for every letter b of p.")),
            Describe.Lean(
                DescribeId.Create("trace-head-exposure"),
                DeclarationHandle.Create("D5/S1/Words/TraceProjection.head_exposure"),
                H("Recovering a head and its residual word"),
                StatementSource.FromAuthor(HeadStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every head a and words r,t, equality E(I,a::r,t) "
                    + "forces a factorization t=p++a::q in which each letter b of p satisfies "
                    + "I(a,b), and E(I,r,p++q) still holds. The diagonal readout first guarantees "
                    + "that a occurs in t. Choose its first occurrence, so p contains no a. "
                    + "If b in p were dependent on a, the (a,b) readout of the source would "
                    + "start with a, while the nonempty readout of p would force a different "
                    + "first letter. This contradiction proves the prefix commutation condition. "
                    + "Actual legal adjacent exchanges move a past p. Their readout invariance "
                    + "and cancellation of the common head give the residual equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-dependent-pair-classification"),
                DeclarationHandle.Create("D5/S1/Words/TraceProjection.connected_iff_same_projections"),
                H("Exact classification by dependent pairs"),
                StatementSource.FromAuthor(ClassificationStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For all words s,t, Connected(I,s,t) holds exactly when "
                    + "E(I,s,t) holds. A legal swap cannot retain both exchanged letters in a "
                    + "dependent-pair readout: retaining both would contradict symmetry or "
                    + "irreflexivity. Thus each step, and every finite sequence of steps, "
                    + "preserves the readouts. Conversely, induction on the source word uses "
                    + "head exposure to recover a commuting prefix and an equal residual "
                    + "observation. Induction connects the residual words, and moving the "
                    + "exposed head back through the prefix reaches the target.")),
                    Paragraph(Text("Empty alphabets and words, infinite alphabets, and repeated "
                        + "letters are included. There is no finiteness, decidable equality, "
                        + "occurrence matching, partial order, or supplied path premise. "
                        + "Classical equality is used internally to define deletion as a native "
                        + "list filter. Cori and Perrin's Proposition 1.1, page 23 with proof on "
                        + "page 24, gives the established finite-alphabet characterization under "
                        + "a reflexive symmetric convention. Here that relation is a=b or I(a,b). "
                        + "The proof itself handles arbitrary alphabets directly. The result "
                        + "asserts existence of a finite legal connection and gives no complexity "
                        + "bound or claim of originality."))),
                DescribeRole.Theorem))));

    private static Formula HeadStatement()
    {
        Formula result = Q(
            V("t"), Eq, Call("append", V("p"), Call("cons", V("a"), V("q"))),
            Land, Call("EveryIndependent", V("I"), V("a"), V("p")),
            Land, Call("E", V("I"), V("r"), Call("append", V("p"), V("q"))));
        foreach (var name in new[] { "q", "p" })
            result = new Formula.Bind(FormulaQuantifier.Exists,
                FormulaIdentifier.Create(name), Call("List", V("alpha")), result);
        return Disp(Q(Call("E", V("I"), Call("cons", V("a"), V("r")), V("t")),
            Implies, result));
    }

    private static Formula ClassificationStatement() => Disp(
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("s"),
            Call("List", V("alpha")),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("t"),
                Call("List", V("alpha")), Q(
                    Call("Connected", V("I"), V("s"), V("t")), Iff,
                    Call("E", V("I"), V("s"), V("t"))))));

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
