using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class DirectionMatchingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/felzenbaumholzman1993packing");

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type,
        Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Statement()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var f = F.Id("f");
        var r = F.Id("r");
        var i = F.Id("i");
        var p = F.Id("p");
        var directions = Call("Directions", n);
        var evenProfiles = Call("EvenProfiles", n);
        var oddProfiles = Call("OddProfiles", n);
        var row = Bind(FormulaQuantifier.ForAll, "p", evenProfiles,
            new Formula.Relation(Call("Value", f, p), FormulaRelationOperator.Equal,
                Call("Flip", p, Call("Value", r, p))));
        var counts = Bind(FormulaQuantifier.ForAll, "i", directions,
            new Formula.Relation(Call("Count", r, i), FormulaRelationOperator.Equal,
                Call("Value", d, i)));
        var matching = Bind(FormulaQuantifier.Exists, "f", Call("Equiv", evenProfiles, oddProfiles),
            Bind(FormulaQuantifier.Exists, "r", new Formula.TypeArrow(evenProfiles, directions),
                new Formula.Logic(Seq(Open, row, Close), FormulaLogicOperator.And,
                    Seq(Open, counts, Close))));
        var even = Bind(FormulaQuantifier.ForAll, "i", directions,
            Call("Even", Call("Value", d, i)));
        var law = new Formula.Logic(Seq(Open, matching, Close), FormulaLogicOperator.Iff,
            Seq(Open, even, Close));
        return Disp(Bind(FormulaQuantifier.ForAll, "n", F.Id("Nat"),
            Bind(FormulaQuantifier.ForAll, "d", new Formula.TypeArrow(directions, F.Id("Nat")),
                new Formula.Logic(Call("Total", n, d), FormulaLogicOperator.Implies,
                    Seq(Open, law, Close)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A perfect matching of a binary cube can realize any even direction counts of the correct total.",
        H("Prescribed directions in a hypercube matching"),
        Blocks(Describe.Lean(
            DescribeId.Create("hypercube-matching-directions"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching.exact_matching_directions"),
            H("Exactly which direction counts a perfect matching can realize"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For a natural number n the cube has n+2 coordinates. " +
                    "Directions(n) is Fin(n+2). EvenProfiles(n) and OddProfiles(n) consist of " +
                    "the binary vectors whose coordinate sum modulo two is zero and one, respectively. " +
                    "Total(n,d) means that the sum of the natural direction counts d(i) is 2^(n+1). " +
                    "Flip(p,i) toggles coordinate i and leaves all other coordinates fixed. " +
                    "Value denotes function evaluation. Count(r,i) counts all even profiles p " +
                    "with r(p)=i. Equiv denotes a bijection. The formula requires every pair " +
                    "to be a coordinate flip and every prescribed count to be attained.")),
                Paragraph(Text("Deleting the first coordinate identifies each parity class with the " +
                    "same additive group of binary tails. A flip of the first coordinate requests " +
                    "zero displacement in the tail. Every other flip requests its unit vector. " +
                    "Even multiplicity of each direction makes the total displacement zero. " +
                    "Hall's theorem numbers the input tails so that adding the requests also " +
                    "numbers the output tails. Restoring the head by parity gives the matching.")),
                Paragraph(Text("For a matching, the input and output tail sums agree because both " +
                    "enumerate the same group. The displacement sum is therefore zero. Each " +
                    "noninitial coordinate of this sum is the corresponding direction count " +
                    "modulo two. The remaining count is even because the total is even."))),
            DescribeRole.Theorem))));
}
