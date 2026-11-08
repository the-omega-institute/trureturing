using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class PlanarSewingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Planar path sewing", H("Planar path sewing"), Blocks(
            Paragraph(Text("NCMatching is a fixed-point-free involutive permutation of a finite cyclic boundary without interleaving chords. BoundaryEquiv lists the top ports from left to right and then the bottom ports from right to left. Finite tagged matching networks are contracted by explicit maps. The adjacent seam relation is equality or one original matching edge or the new seam, closed under equivalence. Repeated adjacent seam elimination gives exactly the path-defined rectangle composite.")),
            Describe.Lean(DescribeId.Create("capstep"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capStep"),
                H("capStep"), StatementSource.FromAuthor(Disp(All("m", Id("Nat"), All("M", Call("NCMatching", Call("Add", Id("m"), Num(2))), All("j", Call("Fin", Call("Add", Id("m"), Num(1))), All("x", Call("Fin", Call("Add", Id("m"), Num(2))), All("y", Call("Fin", Call("Add", Id("m"), Num(2))), Iff(Call("capStep", Id("M"), Id("j"), Id("x"), Id("y")), Or(Equal(Id("y"), Call("partner", Id("M"), Id("x"))), And(Equal(Id("x"), Call("castSucc", Id("j"))), Equal(Id("y"), Call("succ", Id("j"))))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The relation contains each original matching edge and one adjacent seam."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("capsurgery-component-iff"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capSurgery_component_iff"),
                H("capSurgery_component_iff"), StatementSource.FromAuthor(Disp(All("m", Id("Nat"), All("M", Call("NCMatching", Call("Add", Id("m"), Num(2))), All("j", Call("Fin", Call("Add", Id("m"), Num(1))), All("x", Call("Fin", Id("m")), All("y", Call("Fin", Id("m")), Iff(Call("EqvGen", Call("capStep", Id("M"), Id("j")), Call("skipPair", Id("j"), Id("x")), Call("skipPair", Id("j"), Id("y"))), Or(Equal(Id("y"), Id("x")), Equal(Id("y"), Call("partner", Call("capSurgery", Id("M"), Id("j")), Id("x")))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The survivor relation records precisely the reconnection after consuming adjacent ports, including an already paired input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boundaryequiv"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.boundaryEquiv"),
                H("boundaryEquiv"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), Equal(Call("boundaryEquiv", Id("n")), Call("ComposeEquiv", Call("boolProdEquivSum", Call("Fin", Id("n"))), Call("ComposeEquiv", Call("sumCongr", Id("Identity"), Id("Reverse")), Id("finSumFinEquiv"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The final Fin congruence identifies n+n with 2*n. Top(b,i) has value i; bottom(b,i) has value n+(n-1-i)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tomatching"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.toMatching"),
                H("toMatching"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("M", Call("NCMatching", Call("Twice", Id("n"))), Equal(Call("toMatching", Id("M")), Call("MatchingFromInvolution", Call("Conjugate", Call("Inverse", Call("boundaryEquiv", Id("n"))), Call("partner", Id("M")), Call("boundaryEquiv", Id("n"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The conjugation is on the actual endpoints; it forgets only the noncrossing proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("composite-planar"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.composite_planar"),
                H("composite_planar"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("M", Call("NCMatching", Call("Twice", Id("n"))), All("P", Call("NCMatching", Call("Twice", Id("n"))), Ex("Q", Call("NCMatching", Call("Twice", Id("n"))), Equal(Call("toMatching", Id("Q")), Call("composite", Call("toMatching", Id("M")), Call("toMatching", Id("P")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The contraction identifies both endpoint components with the actual composite. Noncrossing closure holds for all products, with any number of internal loops."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-planar"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.identity_planar"),
                H("identity_planar"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), Ex("Q", Call("NCMatching", Call("Twice", Id("n"))), Equal(Call("toMatching", Id("Q")), Call("identityMatching", Id("n"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reverse pairing on the cyclic boundary is the rectangle identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("capreconnection"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capReconnection"),
                H("capReconnection"), StatementSource.FromAuthor(Disp(All("m", Id("Nat"), All("M", Call("NCMatching", Call("Add", Id("m"), Num(2))), All("j", Call("Fin", Call("Add", Id("m"), Num(1))), Equal(Call("capReconnection", Id("M"), Id("j")), Call("NCMatchingFromPartner", Call("capConjugate", Id("M"), Id("j"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("CapConjugate is the conjugation swap(succ(j),partner(castSucc(j))) composed with partner and the same swap. Its partner is an involution without fixed points, and the adjacent reconnection preserves noncrossing."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cupcap-planar"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.cupcap_planar"),
                H("cupcap_planar"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), All("j", Id("Nat"), Imp(Call("Less", Call("Add", Id("j"), Num(1)), Id("n")), Ex("Q", Call("NCMatching", Call("Twice", Id("n"))), Equal(Call("toMatching", Id("Q")), Call("cupcapMatching", Id("j"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The cup-cap matching pairs j,j+1 on each side and sends every other port straight through. It is the adjacent reconnection of the identity."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
