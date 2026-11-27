using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class IrredundantAtomSizesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The irredundant atom sizes of a face of rank at least two form the interval from two to its rank.",
        H("Irredundant atom sizes of a permutohedron face"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rossi-irredundant-atom-sizes"),
                DeclarationHandle.Create(Module + ".exact_spectrum"),
                H("Exact spectrum"),
                StatementSource.FromAuthor(Disp(Spectrum())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Rossi asks in Section 10.3, item 4 which sizes between two and the rank occur for minimal sets of atoms generating a face. Proposition 5.5 of the paper determines the extremal sizes. The grouped exchanges below give the full interval.")),
                    Paragraph(Text("A finite family has distinct members and its join is the lattice supremum, with the empty join equal to bottom. Irredundancy requires the join of every proper subfamily to be strictly below the face. The upper bound uses the integer value of the natural size k.")),
                    Paragraph(Text("Extend the face to a permutation flag. Partition the free prefix ranks into k nonempty groups, and exchange adjacent positions at the ranks of each group to produce one atom. The common cuts recover the face. Each group has a prefix cut that returns upon removing its atom, so every proper subfamily has strictly smaller join.")),
                    Paragraph(Text("For the upper bound, delete one atom at a time and select a cut gained by that deletion. When there are at least three atoms, these cuts have distinct free ranks. The cases of zero, one and two atoms use the bottom, atom and rank conditions directly.")),
                    Paragraph(Text("The separate question about covering all atoms below the face remains open."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rossi-2026-irredundant-atom-sizes"),
                    ResolutionKind.Proved)))));

    private static Formula Spectrum()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var k = F.Id("k");
        var atom = F.Id("a");
        var family = F.Id("A");
        var subfamily = F.Id("B");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var faces = Call("Face", n);
        var families = Call("Finset", faces);
        var rank = Call("rank", x);
        var proper = Seq(subfamily, Sp, Subset, Sp, family);
        var atoms = Bind(FormulaQuantifier.ForAll, "a", faces,
            Logic(Member(atom, family), FormulaLogicOperator.Implies, Call("IsAtom", atom)));
        var deletions = Bind(FormulaQuantifier.ForAll, "B", families,
            Logic(proper, FormulaLogicOperator.Implies,
                Rel(Call("sup", subfamily), FormulaRelationOperator.LessThan, x)));
        var generators = Bind(FormulaQuantifier.Exists, "A", families,
            And(Rel(Call("card", family), FormulaRelationOperator.Equal, k),
                And(Parens(atoms), And(Rel(Call("sup", family), FormulaRelationOperator.Equal, x),
                    Parens(deletions)))));
        var interval = And(Le(D(2), k), Le(Call("int", k), rank));
        return Bind(FormulaQuantifier.ForAll, "n", naturals,
            Logic(Le(D(3), n), FormulaLogicOperator.Implies,
                Bind(FormulaQuantifier.ForAll, "x", faces,
                    Logic(Le(D(2), rank), FormulaLogicOperator.Implies,
                        Bind(FormulaQuantifier.ForAll, "k", naturals,
                            Logic(Parens(generators), FormulaLogicOperator.Iff, Parens(interval)))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Member(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Le(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
}
