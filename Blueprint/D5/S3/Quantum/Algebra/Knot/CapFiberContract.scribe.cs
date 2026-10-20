using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class CapFiberContractDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal-path cap fibers.",
        H("Legal-path cap fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiber"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/CapFiberContract.CapFiberGoal"),
                H("Legal-path cap fibers"), StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, All("L", V("FiniteDecidableType"), All("R", Call("Relation", V("L")), All("q", Call("Function", V("L"), V("Real")), All("s", V("L"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), Equivalent(Call("CapFiberGoal", V("R"), V("q"), V("s"), V("m"), V("M"), V("j")), Exists("N", Call("NCMatching", V("m")), Both(All("k", Call("Fin", V("m")), Equal(Call("SkipPair", V("j"), Call("Partner", V("N"), V("k"))), Call("ReconnectPartner", V("M"), V("j"), Call("SkipPair", V("j"), V("k"))))), All("y", Call("LegalPath", V("R"), V("m"), V("s"), V("s")), Both(Implies(Equal(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Both(All("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Equivalent(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Compatible", V("N"), V("y")))), All("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Equal(Multiply(Call("BoundaryPotential", V("q"), V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Multiply(Call("Square", Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Call("BoundaryPotential", V("q"), V("N"), V("y"))))))), Implies(NotEqual(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Both(Equivalent(Call("Compatible", V("N"), V("y")), Exists("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Both(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), All("c", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Implies(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("c"))), Equal(V("c"), V("b"))))))), All("b", Call("NeighborLabels", V("R"), Call("Apply", V("y"), V("j"))), Implies(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Equal(Multiply(Call("BoundaryPotential", V("q"), V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Call("BoundaryPotential", V("q"), V("N"), V("y"))))))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FiniteDecidableType denotes any finite label type with decidable equality. NeighborLabels(R,a) is the subtype of labels b satisfying R(a,b); formulas involving such a neighbor use its underlying label. Apply is function evaluation, CastSucc and Succ are the left and right gap inclusions, and Square is the ordinary second power. Fix an arbitrary label relation, real label weights, a root, an adjacent cap and a noncrossing matching. The goal requires a smaller matching with the exact rewiring and both complete cap-fiber laws over the existing rooted LegalPath carrier. The closed law quantifies every neighboring middle label and includes the squared ratio. The nonclosed law requires a unique legal neighbor exactly when the smaller labels are compatible, and the exact potential transport for each compatible lift."))),
                DescribeRole.Definition))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
