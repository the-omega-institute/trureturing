using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class LegalCapFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent cap fibers of rooted legal paths.",
        H("Adjacent cap fibers of rooted legal paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("detour"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/LegalCapFibers.legalDetour"),
                H("Adjacent cap fibers of rooted legal paths"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("FiniteDecidableType"), All("R", Call("Relation", V("L")), All("s", V("L"), All("m", V("Natural"), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("LegalPath", V("R"), V("m"), V("s"), V("s")), All("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Implies(Call("Symmetric", V("R")), Equal(Call("UnderlyingLabels", Call("LegalDetour", V("R"), V("s"), V("j"), V("y"), V("b"))), Call("DetourLabels", V("j"), V("y"), V("b"))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A neighbor of the cap gap gives a genuine rooted legal detour of length two more. Symmetry of the relation supplies its reverse edge, the original endpoints stay fixed, and every unaffected edge comes from the original path."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("closed"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/LegalCapFibers.capSurgery_close_fiber"),
                H("Adjacent cap fibers of rooted legal paths"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("FiniteDecidableType"), All("R", Call("Relation", V("L")), All("q", Call("Function", V("L"), V("Real")), All("s", V("L"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("LegalPath", V("R"), V("m"), V("s"), V("s")), Implies(Equal(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Both(All("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Equivalent(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Compatible", Call("CapSurgery", V("M"), V("j")), V("y")))), All("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Equal(Multiply(Call("BoundaryPotential", V("q"), V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Multiply(Call("Square", Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Call("BoundaryPotential", V("q"), Call("CapSurgery", V("M"), V("j")), V("y"))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed compatibility and squared-weight identities hold for the complete neighbor fiber, including empty fibers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonclosed"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/LegalCapFibers.nonclose_legal_fiber"),
                H("Adjacent cap fibers of rooted legal paths"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("FiniteDecidableType"), All("R", Call("Relation", V("L")), All("s", V("L"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("LegalPath", V("R"), V("m"), V("s"), V("s")), Implies(NotEqual(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Implies(Call("Symmetric", V("R")), Equivalent(Call("Compatible", Call("CapSurgery", V("M"), V("j")), V("y")), Exists("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Both(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), All("c", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Implies(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("c"))), Equal(V("c"), V("b")))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonclosed compatible middle label is a genuine neighbor. Its legality follows from the surviving path edge and symmetry, and subtype extensionality gives uniqueness. No nonempty path-space assumption is required."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
