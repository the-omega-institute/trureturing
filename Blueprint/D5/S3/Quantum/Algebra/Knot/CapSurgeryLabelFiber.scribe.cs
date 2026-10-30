using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class CapSurgeryLabelFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary symmetric-label cap surgery.",
        H("Arbitrary symmetric-label cap surgery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cap-fiber"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/CapSurgeryLabelFiber.capSurgery_labelFiber"),
                H("Arbitrary symmetric-label cap surgery"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("FiniteDecidableType"), All("R", Call("Relation", V("L")), All("q", Call("Function", V("L"), V("Real")), All("s", V("L"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), Implies(Call("Symmetric", V("R")), Implies(All("a", V("L"), NotEqual(Call("Apply", V("q"), V("a")), Num(0))), Call("CapFiberGoal", V("R"), V("q"), V("s"), V("m"), V("M"), V("j"))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite label type, every symmetric relation, every everywhere nonzero real weight function, every root, every frontier size and every adjacent cap, the complete CapFiberGoal holds. The smaller noncrossing matching is constructed by the exact rewiring. In the closed case every neighbor lifts and the potential gains the squared cap ratio. In the nonclosed case compatibility is equivalent to existence of a unique legal neighbor, and each compatible lift has the exact potential identity. Self-loops, empty fibers, empty residual frontiers, negative nonzero weights and all nesting patterns remain in scope. This is an algebraic matching and legal-path statement; no circle evaluation, eigenvector hypothesis or topological invariant is asserted."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
